(* Hint Unification *)
signature Hint_Unification =
sig

  type hint = (term * term) * (indexname * (typ * term)) list * thm
  type unifT = Context.generic -> term * term -> Envir.env -> (Envir.env * thm)
  type matchT = theory -> term * term -> Type.tyenv * Envir.tenv -> Type.tyenv * Envir.tenv

  exception Unif of term * term
  exception Occurs_Check of term
  exception Matching_Hints of ((term * term) * hint * exn) list * exn

  val gen_hint_list : Proof.context -> hint list

  val try_hints : Context.generic -> matchT -> unifT -> Envir.env -> (term * term) -> hint list -> (Envir.env * thm) list
  val first_order_unify : Context.generic -> term * term -> Envir.env -> (Envir.env * thm)
  val first_order_unify_h : Context.generic -> term * term -> Envir.env -> (Envir.env * thm)

end

structure HUnif : Hint_Unification =
struct

type hint = (term * term) * (indexname * (typ * term)) list * thm
type unifT = Context.generic -> term * term -> Envir.env -> (Envir.env * thm)
type matchT = theory -> term * term -> Type.tyenv * Envir.tenv -> Type.tyenv * Envir.tenv

exception Unif of term * term
exception Occurs_Check of term
exception Matching_Hints of ((term * term) * hint * exn) list * exn

fun pretty_helper_p aux prems =
  prems |> map aux
        |> map (fn (s1, s2) => Pretty.block [s1, Pretty.str " := ", s2])
        |> Pretty.enum "," "[" "]"

fun pretty_prems ctxt env =
  let
    fun get_trms (v, (T, t)) = (Var (v, T), t)
    val print = apply2 (Syntax.pretty_term ctxt) 
  in pretty_helper_p (print o get_trms) env
end

fun pretty_hint ctxt (_,prems,thm) =
  Pretty.block
    [pretty_prems ctxt prems, Pretty.str " \<Longrightarrow> ", Syntax.pretty_term ctxt (Thm.concl_of thm)]

fun tracing_hint ctxt = (tracing o Pretty.string_of o pretty_hint ctxt)

fun tracing_str_hint ctxt str h = tracing (str ^ (Pretty.string_of (pretty_hint ctxt h)))

fun print_matched_hint ctxt (t1,t2,thm) =
  "Terms "
    ^ Pretty.string_of (pretty_term ctxt t1) ^ ", "
    ^ Pretty.string_of (pretty_term ctxt t2) ^ " matched hint: "
    ^ Pretty.string_of (pretty_thm ctxt thm)

fun print_matching_hints ctxt hs =
  let val _ = tracing "This hint matched but the resulting unification could not be solved:"
  in fold (fn ((t1,t2),(_,_,thm),exn) => fn _ =>
        (tracing (print_matched_hint ctxt (t1,t2,thm));
         Log.debug ctxt (tracing o (fn str => "Exception raised:\n"^str) o @{make_string}) exn)) hs ()
  end


(*theorems reflexity, combination and symmetry*)
val reflexive = @{thm Pure.reflexive}
val combination = Thm.axiom @{theory} "Pure.combination"
val symmetric = @{thm Pure.symmetric}

(*flips a thm using symmetry*)
fun flip_thm thm = symmetric OF [thm]

(*instantiates the first type variable in th with typ*)
fun instantiate_type_var ctxt typ thm =
  Thm.instantiate ([(hd (Term.add_tvars (Thm.full_prop_of thm) []), Thm.ctyp_of ctxt typ)], []) thm

(*instantiates Pure.reflexive with [t/x_0]*)
fun inst_refl ctxt t =
  let val pctxt = Context.proof_of ctxt
      val renamed_refl = instantiate_type_var pctxt (type_of t) reflexive
      val var =  (hd (Term.add_vars (Thm.full_prop_of renamed_refl) []))
      val ct = Thm.cterm_of pctxt t
  in infer_instantiate_types pctxt [(var,ct)] renamed_refl end

(*map function over bound indices, from pattern.ML*)
fun mapbnd f =
  let fun mpb d (Bound (i))    = if i < d then Bound(i) else Bound(f(i-d)+d)
        | mpb d (Abs (s,T,t))  = Abs(s,T,mpb(d+1) t)
        | mpb d (u1 $ u2)      = (mpb d u1)$(mpb d u2)
        | mpb _ atom           = atom
  in mpb 0 end

(*increases all bound indices in a term by 1*)
val incr = mapbnd (fn i => i+1)

(*occurs check*)
fun contains_var v =
  fn Var (x,_)   => x = v
  |  t1 $ t2     => contains_var v t2 orelse contains_var v t1
  |  Abs (_,_,t) => contains_var v t
  |  _           => false

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
  (thm |> Thm.concl_of
       |> (fn (Const ("Pure.eq",_) $ t1 $ t2) => (Envir.eta_contract t1,Envir.eta_contract t2)),
  (thm |> Thm.prems_of
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

(*applies Envir substitutions to thm*)
fun norm_thm ctxt envir thm =
  let val pctxt = Context.proof_of ctxt in
    infer_instantiate pctxt (envir_to_ct_map pctxt envir) thm
  end

(*discharges n prems by applying reflexivity*)
fun discharge_prems thm =
  fn 0 => thm
  |  n => discharge_prems (thm OF [reflexive]) (n-1)

fun unif ctxt env =
  fn
    (Free(x,Tx),Free(y,Ty)) =>
      if x=y then
        let
          val env' = Pattern.unify_types ctxt (Tx,Ty) env
        in
          (env',inst_refl ctxt (Free (x,Envir.norm_type (Envir.type_env env') Tx)))
        end
      else raise Unif (Free(x,Tx),Free(y,Ty))
  | (Const(x,Tx),Const(y,Ty)) =>
      if x=y then
        let
          val env' = Pattern.unify_types ctxt (Tx,Ty) env
        in
          (env',inst_refl ctxt (Const (x,Envir.norm_type (Envir.type_env env') Tx)))
        end
      else raise Unif (Const(x,Tx),Const(y,Ty))
  | (f $ t1,g $ t2) =>
      let
        val (env',thm_fg) = unif ctxt env (f,g)
        val (env'',thm_xy) = unif ctxt env' (Envir.norm_term env' t1, Envir.norm_term env' t2)
      in
        (env'', Thm.combination (norm_thm ctxt env'' thm_fg) (norm_thm ctxt env'' thm_xy))
      end
    | (Var(x,Tx),Var(y,Ty)) =>
        let
          val env' = Pattern.unify_types ctxt (Ty,Tx) env
          val norm_tyenv' = Envir.norm_type (Envir.type_env env')
        in
         (if x=y then env' else Envir.update ((x,norm_tyenv' Tx),Var(y,norm_tyenv' Ty)) env',
          inst_refl ctxt (Var(y,norm_tyenv' Ty)))
        end
    | (Var(x,Tx),t) =>
        if Term.is_open t then raise Unif (Var(x,Tx),t)
         else if contains_var x t then raise Occurs_Check (Var(x,Tx)) else
          (case Envir.lookup env (x,Tx) of
              NONE    => let val env' = Pattern.unify_types ctxt (fastype_of t,Tx) env in
                          (Envir.update ((x,Envir.norm_type (Envir.type_env env') Tx),t) env',inst_refl ctxt t) end
            | SOME t' => if Envir.aeconv (t',t) then (env,inst_refl ctxt t) else unif ctxt env (t',t))
    | (t,Var(x,Tx)) =>
        if Term.is_open t then raise Unif (t,Var(x,Tx))
         else if contains_var x t then raise Occurs_Check (Var(x,Tx)) else
          (case Envir.lookup env (x,Tx) of
              NONE    => let val env' = Pattern.unify_types ctxt (fastype_of t,Tx) env in
                          (Envir.update ((x,Envir.norm_type (Envir.type_env env') Tx),t) env',inst_refl ctxt t) end
            | SOME t' => if Envir.aeconv (t',t) then (env,inst_refl ctxt t) else unif ctxt env (t,t'))
    | (Abs(_,T1,t1),Abs(_,T2,t2)) => unif ctxt (Pattern.unify_types ctxt (T1,T2) env) (t1,t2)
    | (Bound i,Bound j)           => if i=j then (env,inst_refl ctxt (Bound i)) else raise Unif (Bound i,Bound j)
    | (t1,Abs(_,_,t2))            => unif ctxt env (t2,(incr t1)$(Bound 0))
    | (Abs(_,_,t1),t2)            => unif ctxt env (t1,(incr t2)$(Bound 0))
    | (t1,t2) => raise Unif (t1,t2)

fun first_order_unify ctxt (term1,term2) env =
  unif ctxt env
   (Envir.norm_term env term1 |> Envir.eta_contract,
    Envir.norm_term env term2 |> Envir.eta_contract)

(*tries to apply a hint to solve unification of (t1=?t2),
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
      (if flip then flip_thm else I) (hd prem_thms_instd OF (tl prem_thms_instd))
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
          val _ = Log.debug pctxt tracing "Hint matches but cannot unify:"
          val _ = Log.debug pctxt (tracing_hint pctxt) hint
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

(*first order unification with hints*)
fun hint_unify hints ctxt (term1,term2) env =
let
  (*unifies terms, calls try_hint upon failure*)
  fun unif envir (t1,t2) =
  (case (t1,t2) of
      (Free(x,Tx),Free(y,Ty)) =>
        if x=y then
          let
            val env' = Pattern.unify_types ctxt (Ty,Tx) envir
          in
            (env',inst_refl ctxt (Free(x,Envir.norm_type (Envir.type_env env') Tx))) end
        else raise Pattern.Unif
    | (Const(x,Tx),Const(y,Ty)) =>
        if x=y then
          let
            val env' = Pattern.unify_types ctxt (Ty,Tx) envir
          in
            (env',Thm.reflexive (Thm.cterm_of (Context.proof_of ctxt) (Const(x,Envir.norm_type (Envir.type_env env') Tx)))) end
        else raise Pattern.Unif
    | (f $ t1,g $ t2) =>
        let
          val (env',thm_fg) = unif envir (f,g)
          val (env'',thm_xy) = unif env' (Envir.norm_term env' t1, Envir.norm_term env' t2)
        in
          (env'', Thm.combination (norm_thm ctxt env'' thm_fg) (norm_thm ctxt env'' thm_xy))
        end
    | (Var(x,Tx),Var(y,Ty)) =>
        let
          val env' = Pattern.unify_types ctxt (Ty,Tx) envir
          val norm_tyenv' = Envir.norm_type (Envir.type_env env')
        in
         (if x=y then env' else Envir.update ((x,norm_tyenv' Tx),Var(y,norm_tyenv' Ty)) env',
          inst_refl ctxt (Var(y,norm_tyenv' Ty)))
        end
    | (Var(x,Tx),t) =>
        if Term.is_open t then raise Pattern.Unif
        else if contains_var x t then raise Pattern.Unif
        else
          (case Envir.lookup envir (x,Tx) of
             NONE    =>
               let val env' = Pattern.unify_types ctxt (fastype_of t,Tx) envir
               in
                 (Envir.update ((x,Envir.norm_type (Envir.type_env env') Tx),t) env',
                  inst_refl ctxt t)
               end
           | SOME t' =>
               if Envir.aeconv (t',t) then (envir,inst_refl ctxt t')
               else unif envir (t',t))
    | (t,Var(x,Tx)) =>
        if Term.is_open t then raise Pattern.Unif
         else if contains_var x t then raise Pattern.Unif
         else
           (case Envir.lookup envir (x,Tx) of
              NONE    =>
                let val env' = Pattern.unify_types ctxt (fastype_of t,Tx) envir
                in
                  (Envir.update ((x,Envir.norm_type (Envir.type_env env') Tx),t) env',
                   inst_refl ctxt t)
                end
            | SOME t' =>
                if Envir.aeconv (t,t') then (envir,inst_refl ctxt t)
                else unif envir (t,t'))
    | (Bound i,Bound j) => if i=j then (envir,inst_refl ctxt (Bound i))
                           else raise Pattern.Unif
    | (Abs(_,ty1,t1),Abs(_,ty2,t2)) => unif (Pattern.unify_types ctxt (ty1,ty2) envir) (t1,t2)
    | (t1,Abs(_,_,t2))              => unif envir (t2,(incr t1)$(Bound 0))
    | (Abs(_,_,t1),t2)              => unif envir (t1,(incr t2)$(Bound 0))
    | _ => raise Pattern.Unif)
   handle exn =>
     let
       val hint_match_list = (try_hints ctxt Pattern.match first_order_unify_h envir (t1,t2) hints)
     in
       if null hint_match_list then
       raise exn else hd hint_match_list end
in
  let val (sigma,thm) =
    unif
      (Envir.Envir {tenv = Envir.term_env env, tyenv = Envir.type_env env,
       maxidx = Int.max (Envir.maxidx_of env,Int.max (maxidx_of_term term1,maxidx_of_term term2))})
      (term1 |> Envir.norm_term env |> Envir.eta_contract,
       term2 |> Envir.norm_term env |> Envir.eta_contract)
  in (sigma, discharge_prems thm (Thm.nprems_of thm))
  end
end

and
first_order_unify_h ctxt =
  hint_unify (gen_hint_list (Context.proof_of ctxt)) ctxt
  handle Matching_Hints (hs,exn) =>
    let val _ = Log.info (Context.proof_of ctxt) (print_matching_hints (Context.proof_of ctxt)) hs
    in raise exn
    end






end
