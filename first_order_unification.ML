(*  Title:      E_Unification/first_order_unification.ML
    Author:     Kevin Kappelmann, Paul Bachmann

First-order e-unification.
*)
signature FIRST_ORDER_UNIFICATION =
sig
  structure Logger : LOGGER

  val e_unify : Unification_Base.unifier -> Unification_Base.unifier
  val unify : Unification_Base.unifier
  val unify_hints : Unification_Base.unifier
end

structure First_Order_Unification : FIRST_ORDER_UNIFICATION =
struct

structure Logger = @{new_logger "first_order_unification"}

structure Util = Unification_Util

(*occurs check*)
fun occurs v (Var (x, _)) = x = v
  | occurs v (s $ t) = occurs v s orelse occurs v t
  | occurs v (Abs (_, _, t)) = occurs v t
  | occurs _ _ = false

(*first-order e-unification*)
fun e_unify unif_theory ctxt (s, t) env =
  let
    fun rigid_rigid env s (nt, Tt) =
      let val (ns, Ts) = (if is_Const s then dest_Const else dest_Free) s
        in
          if ns = nt then
            (Util.unify_types ctxt (Ts, Tt) env, Unification_Base.reflexive_term ctxt s)
            |> Seq.single
          else raise Unification_Base.UNIF
        end
    fun seq_try sq = Unification_Util.seq_try Unification_Base.UNIF sq
    (*standard first-order unifier that calls unif_fallback on failure*)
    fun unif ctxt binders (s, t) env =
      (case (s, t) of
        (Abs (ns, Ts, ts), Abs (nt, Tt, tt)) =>
          let
            val env' = Util.unify_types ctxt (Ts, Tt) env
            val name = if ns = "" then nt else ns
            val (ctxt', binder as (_, bvar)) = Util.new_binder ctxt name Ts
            val env_thmq = unif ctxt' (binder :: binders) (ts, tt) env' |> seq_try
          in Seq.map (Util.abstract ctxt' name bvar) env_thmq end
      (*eta-expand on the fly*)
      | (Abs (ns, Ts, ts), _) =>
          let
            val (ctxt', binder as (_, bvar)) = Util.new_binder ctxt ns Ts
            val env_thmq = unif ctxt' (binder :: binders) (ts, incr_boundvars 1 t $ Bound 0) env
              |> seq_try
          in Seq.map (Util.abstract ctxt' ns bvar) env_thmq end
      | (_, Abs _) => unif ctxt binders (t, s) env |> Seq.map (apsnd Unification_Base.symmetric)
      | (Bound i, Bound j) =>
          if i = j then
            (env, Util.binder_free binders i |> Unification_Base.reflexive_term ctxt)
            |> Seq.single
          else raise Unification_Base.UNIF
      | (Free f, Free g) => rigid_rigid env (Free f) g
      | (Const c, Const d) => rigid_rigid env (Const c) d
      | (f $ x, g $ y) =>
          let
            val unif' = unif ctxt binders
            val env_thmq = unif' (f, g) env
              |> Seq.maps (fn (env, thm_fg) => unif' (x, y) env |> Seq.map (apsnd (pair thm_fg)))
              |> seq_try
            fun combine (env, thmp) =
              (*normalise types for the combination theorem to succeed*)
              apply2 (Util.norm_thm_types ctxt env) thmp
              |> uncurry Unification_Base.combination
              |> pair env
          in Seq.map combine env_thmq end
      | (Var (x, Tx), _) =>
          let val unif' = unif ctxt binders
          in
            (unif' (Envir.norm_term_same env s, t) env
            handle Same.SAME =>
              (unif' (s, Envir.norm_term_same env t) env
              handle Same.SAME =>
                let val update_env =
                  (*unifying x=x ==> no new term substitution necessary*)
                  if is_Var t andalso x = fst (dest_Var t) then I
                  (*open term and occurs check*)
                  else if Term.is_open t orelse occurs x t then
                    (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
                        Pretty.str "Failed to unify (occurs check or open term) ",
                        Util.pretty_terms ctxt [s, t]
                      ]
                      |> Pretty.string_of);
                    raise Unification_Base.UNIF)
                  (*insert new substitution x \<mapsto> t*)
                  else Envir.vupdate ((x, Tx), t)
                in
                  (Util.unify_types ctxt (Tx, fastype_of t) env,
                    Unification_Base.reflexive_term ctxt s)
                  |>> update_env
                  |> Seq.single
                end))
          end
      | (_, Var _) => unif ctxt binders (t, s) env |> Seq.map (apsnd Unification_Base.symmetric)
      | _ => raise Unification_Base.UNIF)
      handle Unification_Base.UNIF =>
        let
          (*replace all Bounds by Frees to make fallback unification possible*)
          val (s', t') = apply2 (Unification_Util.replace_binders binders) (s, t)
          val _ = @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
              Pretty.str "Failed to (standard) unify; calling theory unifier for ",
              Util.pretty_terms ctxt [s', t']
            ]
            |> Pretty.string_of)
        in unif_theory ctxt (s', t') env end
  in
    (@{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.block [
        Pretty.str "First-order unifying ",
        Util.pretty_terms ctxt (map (Envir.norm_term env) [s, t])
      ]
      |> Pretty.string_of);
    unif ctxt [] (s, t) env)
  end

(*standard first-order unification*)
val unify = e_unify (K o K o K Seq.empty)

(*first-order unification with hints*)
fun unify_hints ctxt =
  let
    val hints = Unification_Hints.gen_hint_list ctxt
    fun unify ctxt =
      e_unify (Unification_Hints.try_hints Pattern.match unify hints) ctxt
  in unify ctxt end

end
