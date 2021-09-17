(*  Title:      Unification_Hints/first_order_unification.ML
    Author:     Kevin Kappelmann, Paul Bachmann

First-order unification with hints.
*)
signature FIRST_ORDER_UNIFICATION =
sig
  structure Logger : LOGGER
  val unify : Unification_Types.unifier
  val unify_hints : Unification_Types.unifier
end

structure First_Order_Unification : FIRST_ORDER_UNIFICATION =
struct

structure Logger = @{new_logger "first_order_unification"}

structure Hints = Unification_Hints
structure Util = Unification_Util

(*occurs check*)
fun occurs v (Var (x, _)) = x = v
  | occurs v (s $ t) = occurs v s orelse occurs v t
  | occurs v (Abs (_, _, t)) = occurs v t
  | occurs _ _ = false

fun unify_core try_hints_fun hints hints_unifier context binders (s, t) =
  let
    val ctxt = Context.proof_of context
    (*standard first-order unifier that calls try_hints_fun on failure*)
    fun unif context binders (s, t) env =
      (case (s, t) of
        (Abs (nx, Tx, tx), Abs (ny, Ty, ty)) =>
          let
            val env' = Util.unify_types context (Tx, Ty) env
            val name = if nx = "" then ny else nx
            val (context', binder as (_, bvar)) = Util.new_binder context name Tx
            val (env'', thm) = unif context' (binder :: binders) (tx, ty) env'
            val bvar' = map_types (Envir.norm_type (Envir.type_env env'')) bvar
            val thm' = Hints.abstract_rule name (Thm.cterm_of (Context.proof_of context') bvar') thm
          in (env'', thm') end
      (*eta-expand on the fly*)
      | (Abs (nx, Tx, tx), _) =>
          let
            val (context', binder as (_, bvar)) = Util.new_binder context nx Tx
            val (env', thm) =
              unif context' (binder :: binders) (tx, incr_boundvars 1 t $ Bound 0) env
            val bvar' = map_types (Envir.norm_type (Envir.type_env env')) bvar
            val thm' = Hints.abstract_rule nx (Thm.cterm_of (Context.proof_of context') bvar') thm
          in (env', thm') end
      | (_, Abs _) => unif context binders (t, s) env ||> Hints.symmetric
      | (Bound i, Bound j) =>
          if i = j then (env, Util.binder_free binders i |> Hints.reflexive_term context)
          else raise Unification_Types.UNIF
      | (Free (x, Tx), Free (y, Ty)) =>
          if x = y then (Util.unify_types context (Tx, Ty) env, Hints.reflexive_term context s)
          else raise Unification_Types.UNIF
      | (Const (x, Tx), Const (y, Ty)) =>
          if x = y then (Util.unify_types context (Tx, Ty) env, Hints.reflexive_term context s)
          else raise Unification_Types.UNIF
      | (f $ x, g $ y) =>
          let
            val unif' = unif context binders
            val (env', thm_fg) = unif' (f, g) env
            val (env'', thm_xy) = unif' (x, y) env'
            (*normalise types for the combination theorem to succeed*)
            val (thm_fg', thm_xy') = apply2 (Util.norm_thm_types ctxt env'') (thm_fg, thm_xy)
          in (env'', Hints.combination thm_fg' thm_xy') end
      | (Var (x, Tx), _) =>
          let val unif' = unif context binders
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
                    raise Unification_Types.UNIF)
                  (*insert new substitution x \<mapsto> t*)
                  else Envir.vupdate ((x, Tx), t)
                in
                  (Util.unify_types context (Tx, fastype_of t) env,
                    Hints.reflexive_term context s)
                  |>> update_env
                end))
          end
      | (_, Var _) => unif context binders (t, s) env ||> Hints.symmetric
      | _ => raise Unification_Types.UNIF)
      handle (exn as Unification_Types.UNIF) =>
        let
          (*replace all Bounds by Frees to make hint matching possible*)
          val (s', t') = Unification_Util.replace_binders binders (s, t)
          val _ = @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
              Pretty.str "Failed to (standard) unify; trying hints for ",
              Util.pretty_terms ctxt [s', t']
            ]
            |> Pretty.string_of)
          val hint_results = try_hints_fun context Pattern.match hints_unifier hints env (s', t')
        in
          case Seq.pull hint_results of
            SOME (res, _) => res
          | NONE =>
              (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
                  Pretty.str "Unification failed for ",
                  Util.pretty_terms ctxt [s', t']
                ]
                |> Pretty.string_of);
              raise exn)
        end
  in
    @{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.block [
        Pretty.str "First-order unifying ",
        Util.pretty_terms ctxt [s, t]
      ]
      |> Pretty.string_of);
    unif context binders (s, t)
  end

(*first-order unification with hints*)
fun unify_hints context =
  unify_core Hints.try_hints (Hints.gen_hint_list (Context.proof_of context)) unify_hints context []

(*standard first-order unification without hints*)
fun unify context = unify_core (K o K o K o K o K o K Seq.empty) [] unify context []

end
