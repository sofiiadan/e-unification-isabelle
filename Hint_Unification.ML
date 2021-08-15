(* Hint Unification *)
signature HINT_UNIFICATION =
sig

  type hint = (term * term) * ((indexname * typ) * term) list * thm
  type unifT = Context.generic -> term * term -> Envir.env -> (Envir.env * thm)
  type matchT = theory -> term * term -> Type.tyenv * Envir.tenv -> Type.tyenv * Envir.tenv

  val reflexive : cterm -> thm
  val combination : thm -> thm -> thm
  val symmetric : thm -> thm
  val reflexive_term : Context.generic -> term -> thm
  val unify_abstraction : Context.generic -> thm -> term -> Envir.env -> thm

  val gen_hint_list : Proof.context -> hint list
  val try_hints : Context.generic -> matchT -> unifT -> Envir.env -> (term * term) -> hint list -> (Envir.env * thm) list
end

structure Hint_Unif : HINT_UNIFICATION =
struct

open Utils

type hint = (term * term) * ((indexname * typ) * term) list * thm
type unifT = Context.generic -> term * term -> Envir.env -> (Envir.env * thm)
type matchT = theory -> term * term -> Type.tyenv * Envir.tenv -> Type.tyenv * Envir.tenv

(*theorems reflexivity, combination and symmetry*)
val reflexive = Thm.reflexive
val combination = Thm.combination
val symmetric = Thm.symmetric
val abstraction = Thm.axiom @{theory} "Pure.abstract_rule";

fun reflexive_term ctxt t =
  reflexive (Thm.cterm_of (Context.proof_of ctxt) t)

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

(*converts Envir into lists of var to cterm and tvar to ctype mappings*)
fun env_lists (Envir.Envir {tenv,tyenv,...}) ctxt =
  (map (fn (xi,(S,T)) => ((xi,S),Thm.ctyp_of ctxt T)) (Vartab.dest tyenv),
   map (fn (xi,(T,t)) => ((xi,T),Thm.cterm_of ctxt t)) (Vartab.dest tenv))

(*converts Envir into var to cterm list without type (for infer_instantiate)*)
fun envir_to_ct_map ctxt env =
  env_lists env ctxt |> snd |> map (fn ((a,_),c) => (a,c))

fun inf_instantiate ctxt env thm = infer_instantiate ctxt (envir_to_ct_map ctxt env) thm

(*increase index of all Vars in term by n*)
fun incr_idx n =
   fn Var ((name,idx),T) => Var ((name,idx+n),T)
   |  Abs (x,T,t)        => Abs (x,T,incr_idx n t)
   |  t1 $ t2            => incr_idx n t1 $ incr_idx n t2
   |  t                  => t

(*increase indeces in a list of substitutions for a hint*)
fun incr_indexes_prems index =
  map (fn (((s,i),T),t) => (((s,i+index),T),incr_idx index t))

(*generates a hint from a theorem,
  returns (SOME hint,"") if successful,
  (NONE,thm_name) otherwise*)
fun gen_hint thm = (SOME
  (case Logic.dest_equals (Thm.concl_of thm) of
     (t1,t2) => (Envir.eta_contract t1,Envir.eta_contract t2),
  (Thm.prems_of thm
     |> map ((fn (Var x,t) => (x,Envir.eta_contract t)) o Logic.dest_equals)),
    Drule.eta_contraction_rule thm),"")
  handle
    Match => (NONE,Thm.derivation_name thm)
   |TERM _ => (NONE,Thm.derivation_name thm)

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
        Logger.info ctxt tracing
          ("These theorems cannot be used as hints: \n"^ String.concatWith ", " thm_strs)
  in
    hs |> filter Option.isSome
       |> map Option.valOf
       |> rev
  end

(*tries to apply a hint to solve E-unification of (t1\<equiv>?t2),
  Vars in hint are renamed to avoid naming conflicts during matching,
  matches the pattern with (t1,t2) using match,
  unifies resulting unification problems using unif,
  returns SOME (env,thm) if successfull,*)
fun try_hint context match unif
  (Envir.Envir {maxidx,tenv,tyenv}) (t1,t2)
  (hint as ((P_raw,Q_raw),hint_prems_raw,hint_thm_raw)) =
  let
    val ctxt = Context.proof_of context

    val _ = Logger.debug ctxt (tracing_str_hint ctxt "Trying hint: ") hint

    (*increase indices in hints to avoid naming conflicts*)
    val (P,Q) =
      (incr_idx (maxidx+1) P_raw,incr_idx (maxidx+1) Q_raw)
    val hint_prems =
      incr_indexes_prems (maxidx+1) hint_prems_raw
    val maxidx_new =
      Int.max (maxidx,Int.max (maxidx_of_term P,maxidx_of_term Q))
    val hint_thm =
      Thm.incr_indexes (maxidx+1) hint_thm_raw

    (*match hint with unification pair, set flip if hint matches flipped*)
    val pmatch = match (Context.theory_of context)
    val ((match_tyenv,match_tenv),flip) = ((pmatch (Q,t2) (pmatch (P,t1) (tyenv,tenv)),false)
      handle Pattern.MATCH => ((pmatch (P,t2) (pmatch (Q,t1) (tyenv,tenv))),true))
    val match_env =
      Envir.Envir {tyenv=match_tyenv,tenv=match_tenv,maxidx=maxidx_new}
    val hint_thm_matched =  
      inf_instantiate ctxt match_env hint_thm

    val _ = Logger.debug ctxt tracing "Hint matches, now unifying hint premises..."

    (*unify each hint premise, returning an (env,thm) list*)
    fun prem_foldfun (x,s) env_thms =
      let val (envir,_) = hd env_thms in
        unif context (Envir.norm_term match_env (Var x),Envir.norm_term match_env s) envir
          :: env_thms
      end
    val prem_env_thms =
      fold prem_foldfun hint_prems
         [(Envir.Envir {maxidx=maxidx_new,tenv=match_tenv,tyenv=match_tyenv},hint_thm_matched)]

    (*instantiate the theorems for the premises with the envs returned from last to first*)
    val prem_thms_instd =
      fold_rev
        (fn (env,thm) => fn thms_acc =>
            (map (inf_instantiate ctxt env) thms_acc) @ [inf_instantiate ctxt env thm])
        prem_env_thms []

    (*discharge the hint premises using the instantiated premise theorems, flip theorem if needed*)
    val thm_return =
      (if flip then symmetric else I) (hd prem_thms_instd OF (tl prem_thms_instd))
    val (envir_return,_) = hd prem_env_thms
    val _ = Logger.debug ctxt (fn thm =>
      tracing ("All premises unified, resulting theorem: "^Pretty.string_of (pretty_thm ctxt thm))) thm_return
  in
    SOME (envir_return,thm_return)
  end
    handle
      Pattern.MATCH =>
        (Logger.debug (Context.proof_of context) tracing "Hint does not match"; NONE)
    | _ =>
        let val ctxt = Context.proof_of context in
          (Logger.debug ctxt (tracing_str_hint ctxt "Hint matches but cannot unify:") hint; NONE)
        end

(*try to apply every hint from the hint list*)
fun try_hints ctxt match unif envir (t1,t2) =
  let
    val pctxt = Context.proof_of ctxt
    val _ = Logger.debug pctxt (fn ts =>
      tracing ("Trying hints for subterms: "^Pretty.string_of (pretty_terms pctxt ts))) [t1,t2]
  in
    map Option.valOf
     o filter Option.isSome
     o map (try_hint ctxt match unif envir (t1,t2))
  end




end
