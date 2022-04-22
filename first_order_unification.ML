(*  Title:      E_Unification/first_order_unification.ML
    Author:     Kevin Kappelmann, Paul Bachmann

First-order E-unification.
*)
signature FIRST_ORDER_UNIFICATION =
sig
  structure Logger : LOGGER

  val e_match : Unification_Base.type_matcher -> Unification_Base.matcher ->
    Unification_Base.matcher
  val match : Unification_Base.matcher
  val match_hints : Unification_Base.matcher

  val e_unify : Unification_Base.type_unifier -> Unification_Base.unifier ->
    Unification_Base.unifier
  val unify : Unification_Base.unifier
  val unify_hints : Unification_Base.unifier

end

structure First_Order_Unification : FIRST_ORDER_UNIFICATION =
struct

(* shared utils *)

structure Logger = @{new_logger "first_order_unification"}

structure Util = Unification_Util

(*check if sequence is empty or raise UNIF exception*)
fun seq_try sq = Util.seq_try Unification_Base.UNIF sq

(*occurs check*)
fun occurs v (Var (x, _)) = x = v
  | occurs v (s $ t) = occurs v s orelse occurs v t
  | occurs v (Abs (_, _, t)) = occurs v t
  | occurs _ _ = false

(* first-order E-matching *)
(*Note: by E-matching we mean "matching modulo equalities" in the general sense,
i.e. when matching p \<equiv>? t, t may contain variables.*)
fun e_match match_types match_theory ctxt (p, t) env =
  let
    (*standard first-order matcher that calls match_theory on failure*)
    fun match binders ctxt (p, t) (env as Envir.Envir {tenv, tyenv,...}) =
      (case (p, t) of
        (Abs (np, Tp, tp), Abs (nt, Tt, tt)) =>
          let
            val env' = match_types ctxt (Tp, Tt) env
            val name = if np = "" then nt else np
            val (ctxt', binder as (_, bvar)) = Util.new_binder ctxt name Tt
          in
            match (binder :: binders) ctxt' (tp, tt) env'
            |> seq_try
            (*Note: types of binders are already fixed to the object's binder's type
            ==> we pass the identity type normaliser*)
            |> Util.norm_abstract_env_thmq (K I) ctxt' name bvar
          end
      (*eta-expand on the fly*)
      | (Abs (np, Tp, tp), _) =>
          let
            val Tt = Envir.subst_type tyenv Tp
            val (ctxt', binder as (_, bvar)) = Util.new_binder ctxt np Tt
          in
            match (binder :: binders) ctxt' (tp, incr_boundvars 1 t $ Bound 0) env
            |> seq_try
            |> Util.norm_abstract_env_thmq (K I) ctxt' np bvar
          end
      | (_, Abs (nt, Tt, tt)) =>
          let val (ctxt', binder as (_, bvar)) = Util.new_binder ctxt nt Tt
          in
            match (binder :: binders) ctxt' (incr_boundvars 1 p $ Bound 0, tt) env
            |> seq_try
            |> Util.norm_abstract_env_thmq (K I) ctxt' nt bvar
          end
      | (Bound i, Bound j) => Util.bound_bound ctxt i j binders |> seq_try |> Seq.map (pair env)
      | (Free _, Free g) =>
          (*normalise the types in rigid-rigid cases*)
          Util.rigid_rigid (map_types o Util.norm_type_match) match_types ctxt p g env
          |> seq_try
      | (Const _, Const d) =>
          Util.rigid_rigid (map_types o Util.norm_type_match) match_types ctxt p d env
          |> seq_try
      | (f $ x, g $ y) =>
          (*Note: types of recursive theorems are already normalised ==> we have to
          pass the identity type normaliser*)
          Util.comb_comb (K o K I) (match binders) ctxt (f, x) (g, y) env |> seq_try
      | (Var (x, Tx), _) =>
          (case Envir.lookup1 tenv (x, Util.norm_type_match tyenv Tx) of
            NONE =>
              let
                val Tt = fastype_of t
                val try_update_env =
                  (*open term check*)
                  if Term.is_open t then
                    (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
                        Pretty.str "Failed to match (open term) ",
                        Util.pretty_unif ctxt (p, t)
                      ]
                      |> Pretty.string_of);
                    raise Unification_Base.UNIF)
                  (*insert new substitution x \<mapsto> t*)
                  else Envir.update ((x, Tt), t)
              in
                (match_types ctxt (Tx, Tt) env,
                  Unification_Base.reflexive_term ctxt t)
                |>> try_update_env
                |> Seq.single
              end
          | SOME p' =>
            if Envir.aeconv (apply2 Envir.beta_norm (p', t)) then
              Seq.single (env, Unification_Base.reflexive_term ctxt t)
            else raise Unification_Base.UNIF)
      | _ => raise Unification_Base.UNIF)
      handle Unification_Base.UNIF =>
        let
          (*replace all Bounds by Frees so that the theory matcher receives a closed term*)
         val (p', t') = apply2 (Util.replace_binders binders) (p, t)
            |> apfst (Util.norm_term_match env)
          val _ = @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
              Pretty.str "Failed to (standard) match; calling theory matcher for ",
              Util.pretty_unif ctxt (p', t')
            ]
            |> Pretty.string_of)
        in match_theory ctxt (p', t') env end
  in
    (@{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.block [
        Pretty.str "First-order matching ",
        Util.pretty_unif ctxt (Util.norm_term_match env p, t)
      ]
      |> Pretty.string_of);
    match [] ctxt (p, t) env)
  end

(*standard first-order matching*)
val match = e_match Util.match_types (K o K o K Seq.empty)

(*first-order matching with hints*)
fun match_hints ctxt =
  let
    val ctxt' = Config.put Unification_Hints.try_symmetric false ctxt
    val hints = Unification_Hints.gen_hint_list ctxt
    val norm_thm_match = Util.norm_thm Util.norm_type_match Util.norm_term_match
    val norm_thm_unif = K o K I
    fun match ctxt =
      e_match Util.match_types
        (Unification_Hints.try_hints norm_thm_match Higher_Order_Pattern_Unification.match
        norm_thm_unif match hints)
        ctxt
  in match ctxt' end

(* first-order E-unification *)
fun e_unify unify_types unify_theory ctxt (s, t) env =
  let
    (*standard first-order unifier that calls unify_theory on failure*)
    fun unif binders ctxt (s, t) env =
      (case (s, t) of
        (Abs (ns, Ts, ts), Abs (nt, Tt, tt)) =>
          let
            val env' = unify_types ctxt (Ts, Tt) env
            val name = if ns = "" then nt else ns
            val (ctxt', binder as (_, bvar)) = Util.new_binder ctxt name Ts
          in
            unif (binder :: binders) ctxt' (ts, tt) env'
            |> seq_try
            |> Util.norm_abstract_env_thmq (map_types o Util.norm_type_unif) ctxt' name bvar
          end
      (*eta-expand on the fly*)
      | (Abs (ns, Ts, ts), _) =>
          let val (ctxt', binder as (_, bvar)) = Util.new_binder ctxt ns Ts
          in
            unif (binder :: binders) ctxt' (ts, incr_boundvars 1 t $ Bound 0) env
            |> seq_try
            |> Util.norm_abstract_env_thmq (map_types o Util.norm_type_unif) ctxt' ns bvar
          end
      | (_, Abs _) => unif binders ctxt (t, s) env |> Seq.map (apsnd Unification_Base.symmetric)
      | (Bound i, Bound j) => Util.bound_bound ctxt i j binders |> seq_try |> Seq.map (pair env)
      (*we do not have to normalise types in rigid-rigid cases*)
      | (Free _, Free g) => Util.rigid_rigid (K I) unify_types ctxt s g env |> seq_try
      | (Const _, Const d) => Util.rigid_rigid (K I) unify_types ctxt s d env |> seq_try
      (*but we have to normalise types in comb cases*)
      | (f $ x, g $ y) =>
          Util.comb_comb (Util.norm_thm_types Util.norm_type_unif) (unif binders) ctxt
            (f, x) (g, y) env
          |> seq_try
      | (Var (x, Tx), _) =>
          let val unif' = unif binders ctxt
          in
            (unif' (Envir.norm_term_same env s, t) env
            handle Same.SAME =>
              (unif' (s, Envir.norm_term_same env t) env
              handle Same.SAME =>
                let val try_update_env =
                  (*unifying x=x ==> no new term substitution necessary*)
                  if is_Var t andalso x = fst (dest_Var t) then I
                  (*open term and occurs check*)
                  else if Term.is_open t orelse occurs x t then
                    (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
                        Pretty.str "Failed to unify (occurs check or open term) ",
                        Util.pretty_unif ctxt (s, t)
                      ]
                      |> Pretty.string_of);
                    raise Unification_Base.UNIF)
                  (*insert new substitution x \<mapsto> t*)
                  else Envir.vupdate ((x, Tx), t)
                in
                  (unify_types ctxt (Tx, fastype_of t) env,
                    Unification_Base.reflexive_term ctxt s)
                  |>> try_update_env
                  |> Seq.single
                end))
          end
      | (_, Var _) => unif binders ctxt (t, s) env |> Seq.map (apsnd Unification_Base.symmetric)
      | _ => raise Unification_Base.UNIF)
      handle Unification_Base.UNIF =>
        let
          (*replace all Bounds by Frees so that the theory unifier receives a closed term*)
          val (s', t') =
            apply2 (Util.norm_term_unif env o Util.replace_binders binders) (s, t)
          val _ = @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
              Pretty.str "Failed to (standard) unify; calling theory unifier for ",
              Util.pretty_unif ctxt (s', t')
            ]
            |> Pretty.string_of)
        in unify_theory ctxt (s', t') env end
  in
    (@{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.block [
        Pretty.str "First-order unifying ",
        Util.pretty_unif ctxt (apply2 (Util.norm_term_unif env) (s, t))
      ]
      |> Pretty.string_of);
    unif [] ctxt (s, t) env)
  end

(*standard first-order unification*)
val unify = e_unify Util.unify_types (K o K o K Seq.empty)

(*first-order unification with hints*)
fun unify_hints ctxt =
  let
    val hints = Unification_Hints.gen_hint_list ctxt
    (*no normalisation after matching required since all results are normalised by norm_thm_unif*)
    val norm_thm_match = K o K I
    val norm_thm_unif = Util.norm_thm Util.norm_type_unif Util.norm_term_unif
    fun unify ctxt =
      e_unify Util.unify_types
        (Unification_Hints.try_hints norm_thm_match Higher_Order_Pattern_Unification.match
        norm_thm_unif unify hints)
        ctxt
  in unify ctxt end


end
