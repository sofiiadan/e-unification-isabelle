signature FO_HINT_UNIFICATION =
sig

  val fo_unify : Context.generic -> term * term -> Envir.env -> (Envir.env * thm)
  val fo_unify_hints : Context.generic -> term * term -> Envir.env -> (Envir.env * thm)

end

structure FO_Hint_Unif : FO_HINT_UNIFICATION =
struct

open Utils
open Hint_Unif

exception Unif of term * term
exception Occurs_Check of term

(*map function over bound indices, from pattern.ML*)
fun mapbnd f =
  let fun mpb d (Bound (i))    = if i < d then Bound(i) else Bound(f(i-d)+d)
        | mpb d (Abs (s,T,t))  = Abs(s,T,mpb(d+1) t)
        | mpb d (u1 $ u2)      = (mpb d u1)$(mpb d u2)
        | mpb _ atom           = atom
  in mpb 0 end

(*increases all bound indices in a term by 1*)
val incr = mapbnd (fn i => i+1)

(*discharges n prems by applying reflexivity*)
fun discharge_prems context thm n =
  let
    val refl = reflexive (Thm.cterm_of (Context.proof_of context) (Var(("x",0),TVar(("'a",0),[]))))
  in thm OF (replicate n refl) end

(*converts Envir into lists of var to cterm and tvar to ctype mappings*)
fun env_lists (Envir.Envir {tenv,tyenv,...}) ctxt =
  (map (fn (xi,(S,T)) => ((xi,S),Thm.ctyp_of ctxt T)) (Vartab.dest tyenv),
   map (fn (xi,(T,t)) => ((xi,T),Thm.cterm_of ctxt t)) (Vartab.dest tenv))

(*converts Envir into var to cterm list without type (for infer_instantiate)*)
fun envir_to_ct_map ctxt env = env_lists env ctxt |> snd |> map (fn ((a,_),c) => (a,c))

(*applies Envir substitutions to thm*)
fun norm_thm ctxt envir thm =
  let val pctxt = Context.proof_of ctxt in
    infer_instantiate pctxt (envir_to_ct_map pctxt envir) thm
  end

(*occurs check*)
fun contains_var v =
  fn Var (x,_)   => x = v
  |  t1 $ t2     => contains_var v t2 orelse contains_var v t1
  |  Abs (_,_,t) => contains_var v t
  |  _           => false

(*first order unification with hints*)
fun fo_unification try_hints_fun hints context (term1, term2) env =
let
  (*unifies terms, calls try_hint upon failure*)
  fun unif try_hints_fun envir (t1,t2) =
  (case (t1,t2) of
      (Free(x,Tx),Free(y,Ty)) =>
        if x=y then
          let
            val env' = Pattern.unify_types context (Ty,Tx) envir
            val T = Envir.norm_type (Envir.type_env env') Tx
          in
            (env',reflexive_term context (Free(x,T))) end
        else raise Pattern.Unif
    | (Const(x,Tx),Const(y,Ty)) =>
        if x=y then
          let
            val env' = Pattern.unify_types context (Ty,Tx) envir
            val T = Envir.norm_type (Envir.type_env env') Tx
          in
            (env',reflexive_term context (Const(x,T))) end
        else raise Pattern.Unif
    | (f $ t1,g $ t2) =>
        let
          val (env',thm_fg) = unif try_hints_fun envir (f,g)
          val (env'',thm_xy) = unif try_hints_fun env' (Envir.norm_term env' t1, Envir.norm_term env' t2)
        in
          (env'',combination (norm_thm context env'' thm_fg) (norm_thm context env'' thm_xy))
        end
    | (Var(x,Tx),Var(y,Ty)) =>
        let
          val env' = Pattern.unify_types context (Ty,Tx) envir
          val T = Envir.norm_type (Envir.type_env env') Tx
        in
         (if x=y then env' else Envir.update ((x,T),Var(y,T)) env',
          reflexive_term context (Var(y,T)))
        end
    | (Var(x,Tx),t) =>
        if Term.is_open t then raise Pattern.Unif
        else if contains_var x t then raise Pattern.Unif
        else
          (case Envir.lookup envir (x,Tx) of
             NONE    =>
               let val env' = Pattern.unify_types context (fastype_of t,Tx) envir
               in
                 (Envir.update ((x,Envir.norm_type (Envir.type_env env') Tx),t) env',
                  reflexive_term context t)
               end
           | SOME t' =>
               if Envir.aeconv (t',t)
                 then (envir,reflexive_term context t')
                 else unif try_hints_fun envir (t',t))
    | (t,Var(x,Tx)) =>
        if Term.is_open t then raise Pattern.Unif
         else if contains_var x t then raise Pattern.Unif
         else
           (case Envir.lookup envir (x,Tx) of
              NONE    =>
                let val env' = Pattern.unify_types context (fastype_of t,Tx) envir
                in
                  (Envir.update ((x,Envir.norm_type (Envir.type_env env') Tx),t) env',
                   reflexive_term context t)
                end
            | SOME t' =>
                if Envir.aeconv (t,t')
                  then (envir,reflexive_term context t)
                  else unif try_hints_fun envir (t,t'))
    | (Bound i,Bound j) =>
        if i=j then (envir,reflexive_term context (Bound i))  (**)
               else raise Pattern.Unif
    | (Abs(_,ty1,t1),Abs(_,ty2,t2)) =>
        unif try_hints_fun (Pattern.unify_types context (ty1,ty2) envir) (t1,t2)
    | (t1,Abs(_,_,t2))              => unif try_hints_fun envir (t2,(incr t1)$(Bound 0))
    | (Abs(_,_,t1),t2)              => unif try_hints_fun envir (t1,(incr t2)$(Bound 0))
    | _ => raise Pattern.Unif)
   handle exn =>
     let
       val hint_match_list = (try_hints_fun context Pattern.match fo_unify_hints envir (t1,t2) hints)
     in
       if null hint_match_list then
       raise exn else hd hint_match_list end
in
  let val (sigma,thm) =
    unif try_hints_fun
      (Envir.Envir {tenv = Envir.term_env env, tyenv = Envir.type_env env,
       maxidx = Int.max (Envir.maxidx_of env,Int.max (maxidx_of_term term1,maxidx_of_term term2))})
      (term1 |> Envir.norm_term env |> Envir.eta_contract,
       term2 |> Envir.norm_term env |> Envir.eta_contract)
  in (sigma, discharge_prems context thm (Thm.nprems_of thm))
  end
end

(*first-order unification with hints from context*)
and fo_unify_hints ctxt = fo_unification try_hints (gen_hint_list (Context.proof_of ctxt)) ctxt

(*first-order unification without hints*)
and fo_unify ctxt = fo_unification (K o K o K o K o K o K []) [] ctxt;


end