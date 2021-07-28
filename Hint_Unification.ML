(* Hint Unification *)
signature HINT_UNIFICATION =
sig

  type hint = (term * term) * (indexname * (typ * term)) list * thm
  type unifT = Context.generic -> term * term -> Envir.env -> (Envir.env * thm)
  type matchT = theory -> term * term -> Type.tyenv * Envir.tenv -> Type.tyenv * Envir.tenv

  val reflexive : cterm -> thm
  val combination : thm -> thm -> thm
  val symmetric : thm -> thm
  val unify_abstraction : Context.generic -> thm -> term -> Envir.env -> thm

  val gen_hint_list : Proof.context -> hint list
  val try_hints : Context.generic -> matchT -> unifT -> Envir.env -> (term * term) -> hint list -> (Envir.env * thm) list
end

structure Hint_Unif : HINT_UNIFICATION =
struct

open Utils

type hint = (term * term) * (indexname * (typ * term)) list * thm
type unifT = Context.generic -> term * term -> Envir.env -> (Envir.env * thm)
type matchT = theory -> term * term -> Type.tyenv * Envir.tenv -> Type.tyenv * Envir.tenv

(*theorems reflexivity, combination and symmetry*)
val reflexive = Thm.reflexive
val combination = Thm.combination
val symmetric = Thm.symmetric
val abstraction = Thm.axiom @{theory} "Pure.abstract_rule";


(*converts Envir into lists of var to cterm and tvar to ctype mappings*)
fun env_lists (Envir.Envir {tenv,tyenv,...}) ctxt =
  (map (fn (xi,(S,T)) => ((xi,S),Thm.ctyp_of ctxt T)) (Vartab.dest tyenv),
   map (fn (xi,(T,t)) => ((xi,T),Thm.cterm_of ctxt t)) (Vartab.dest tenv))

(*converts Envir into var to cterm list without type (for infer_instantiate)*)
fun envir_to_ct_map ctxt env = env_lists env ctxt |> snd |> map (fn ((a,_),c) => (a,c))

(*converts idx, type and term environment into Envir*)
fun idx_envs_to_envir idx (tyenv,tenv) = Envir.Envir {tyenv=tyenv,tenv=tenv,maxidx=idx}

(*converts Envir into type and term environment*)
fun envir_to_envs (Envir.Envir {tyenv,tenv,...}) = (tyenv,tenv)

(*increase index of all Vars in term by n*)
fun incr_idx n =
   fn Var ((name,idx),T) => Var ((name,idx+n),T)
   |  Abs (x,T,t)        => Abs (x,T,incr_idx n t)
   |  t1 $ t2            => incr_idx n t1 $ incr_idx n t2
   |  t                  => t

(*increase indeces in a list of substitutions for a hint*)
fun incr_indexes_prems index =
  map (fn ((s,i),(T,t)) => ((s,i+index),(T,incr_idx index t)))

(*generates a hint from a theorem,
  returns (SOME hint,"") if successful,
  (NONE,thm_name) otherwise*)
fun gen_hint thm = (SOME
  (case Thm.concl_of thm of
     Const ("Pure.eq",_) $ t1 $ t2 => (Envir.eta_contract t1,Envir.eta_contract t2),
  (Thm.prems_of thm
     |> map (fn ((Const ("Pure.eq",_) $ Var (x,Tx) $ t)) => (x,(Tx,Envir.eta_contract t)))),
    Drule.eta_contraction_rule thm),"")
  handle Match => (NONE,Thm.derivation_name thm)

(*generates a list of hints from named theorems "hints"*)
fun gen_hint_list ctxt =
  let
    val (hs,strs) =
      Proof_Context.get_thms ctxt "hints"
        |> map gen_hint
        |> ListPair.unzip
    val thm_strs = filter (fn x => x <> "") strs
    val _ =
      if null thm_strs then ()
      else
        Log.info ctxt tracing
          ("These theorems cannot be used as hints: \n"^ String.concatWith ", " thm_strs)
  in
    hs |> filter Option.isSome
       |> map Option.valOf
       |> rev
  end

(*tries to apply a hint to solve E-unification of (t1\<equiv>?t2),
  Vars in hint are renamed to avoid naming conflicts during matching,
  returns SOME (Envir,thm) if successfull,
  unifies resulting unification problems using unif*)
fun try_hint ctxt match unif
  (Envir.Envir {maxidx,tenv,tyenv}) (t1,t2)
  (hint as ((h1_raw,h2_raw),hint_prems_raw,hint_thm_raw)) =
  let
    val pctxt = Context.proof_of ctxt

    val _ = Log.debug pctxt (tracing_str_hint pctxt "Trying hint: ") hint

    (*increase indeces in hints to avoid naming conflicts*)
    val (h1,h2) =
      (incr_idx (maxidx+1) h1_raw,incr_idx (maxidx+1) h2_raw)
    val hint_prems =
      incr_indexes_prems (maxidx+1) hint_prems_raw
    val maxidx_new =
      Int.max (maxidx,Int.max (maxidx_of_term h1,maxidx_of_term h2))
    val hint_thm =
      Thm.incr_indexes (maxidx+1) hint_thm_raw

    (*match hint with unification pair, set flip if hint matches flipped*)
    val pmatch = match (Context.theory_of ctxt)
    fun inf_instantiate env thm = infer_instantiate pctxt (envir_to_ct_map pctxt env) thm
    val unif_envs = (tyenv,tenv)
    val (match_envs,flip) = ((pmatch (h2,t2) (pmatch (h1,t1) unif_envs),false)
      handle Pattern.MATCH => ((pmatch (h1,t2) (pmatch (h2,t1) unif_envs)),true))
    val match_envir = idx_envs_to_envir maxidx_new match_envs
    val (match_tyenv,match_tenv) = envir_to_envs match_envir
    val hint_thm_matched = inf_instantiate match_envir hint_thm

    val _ = Log.debug pctxt tracing "Hint matches, now unifying hint premises..."

    (*unify each hint premise, returning an (Envir,thm) list*)
    fun prem_foldfun (v,(Tv,term)) envir_thms =
      let val (envir,_) = hd envir_thms in
        unif ctxt
          (Envir.lookup match_envir (v,Tv) |> Option.valOf,
           Envir.norm_term match_envir term) envir
        :: envir_thms
      end
    val prem_envir_thms =
      fold prem_foldfun hint_prems
         [(Envir.Envir {maxidx=maxidx_new,tenv=match_tenv,tyenv=match_tyenv},hint_thm_matched)]

    (*instantiate the theorems for the premises with the Envirs returned from last to first*)
    val prem_thms_instd =
      fold_rev
        (fn (env,thm) => fn thms_acc => (map (inf_instantiate env) thms_acc) @ [inf_instantiate env thm])
        prem_envir_thms []

    (*discharge the hint premises using the instantiated premise theorems, flip theorem if needed*)
    val thm_return =
      (if flip then symmetric else I) (hd prem_thms_instd OF (tl prem_thms_instd))
    val (envir_return,_) = hd prem_envir_thms
    val _ = Log.debug pctxt (fn thm =>
      tracing ("All premises unified, resulting theorem: "^Pretty.string_of (pretty_thm pctxt thm))) thm_return
  in
    SOME (envir_return,thm_return)
  end
    handle
      Pattern.MATCH =>
        let
          val pctxt = Context.proof_of ctxt
          val _ = Log.debug pctxt tracing "Hint does not match"
        in NONE end
    | _ =>
        let
          val pctxt = Context.proof_of ctxt
          val _ = Log.debug pctxt (tracing_str_hint pctxt "Hint matches but cannot unify:") hint
        in NONE end

(*try to apply every hint from the hint list*)
fun try_hints ctxt match unif envir (t1,t2) =
  let
    val pctxt = Context.proof_of ctxt
    val _ = Log.debug pctxt (fn ts =>
      tracing ("Trying hints for subterms: "^Pretty.string_of (pretty_terms pctxt ts))) [t1,t2]
  in
  (map Option.valOf
    o filter Option.isSome
    o map (try_hint ctxt match unif envir (t1,t2)))
  end

(*unifies the abstraction theorem with a theorem for a given var*)
fun unify_abstraction ctxt thm var env =
  let
    val pctxt = Context.proof_of ctxt
    val abstr = Thm.incr_indexes (Envir.maxidx_of env+1) abstraction
    val abstr_prem_t = Thm.prems_of abstr |> hd
    val thm_forall = forall_intr_list [Thm.cterm_of pctxt var] thm
    val thm_forall_t = Thm.concl_of thm_forall
    val unif_env = Pattern.unify ctxt (abstr_prem_t,thm_forall_t) env
    val inst_list = map
      (fn (idxn,(_,t)) => (idxn,Thm.cterm_of pctxt (Envir.norm_term unif_env t)))
      (Envir.term_env unif_env |> Vartab.dest)
    val abstr_inst = Drule.infer_instantiate pctxt inst_list abstr
  in
    abstr_inst OF [thm]
  end


end
