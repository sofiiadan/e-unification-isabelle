(*  Title:      E_Unification/higher_order_unification.ML
    Author:     Kevin Kappelmann TU Muenchen

Higher-order unification from the Pure kernel adjusted to fit the
Unification_Base.unifier type, i.e. moving flex-flex pairs into the theorem.
*)
signature HIGHER_ORDER_UNIFICATION =
sig
  structure Logger : LOGGER
  val unify : Unification_Base.unifier
end

structure Higher_Order_Unification : HIGHER_ORDER_UNIFICATION =
struct

structure Logger = @{new_logger "higher_order_unification"}

structure Util = Unification_Util

fun unify ctxt tp env =
  let
    fun unif () =
      let
        val env = Util.unify_types ctxt (apply2 Term.fastype_of tp) env
        val init_goal = Logic.mk_equals #> Thm.cterm_of ctxt #> Goal.init
        fun create_env_thmq env =
          (*apply the computed unifier*)
          apply2 (Util.norm_term_unif env) tp
          (*create a goal such that we can create a theorem including the
            flex-flex pairs*)
          |> init_goal
          (*kind of a hack: resolving against the equality theorem will add the
            flex-flex pairs to the theorem*)
          |> HEADGOAL (resolve_tac ctxt [@{thm Pure.reflexive}])
          (*conclude the goal and pair with the environment*)
          |> Seq.map (pair env o Goal.conclude)
      in
        (*find the unifier*)
        Unify.hounifiers (Context.Proof ctxt, env, [tp])
        (*add the flex-flex pairs to the theorem to fit the unifier signature*)
        |> Seq.maps (create_env_thmq o fst)
        |> tap (@{print} o Seq.list_of)
      end
      handle Unification_Base.UNIF =>
        let
          val tp' = apply2 (Util.norm_term_unif env) tp
          val _ = @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
              Pretty.str "Higher-order unification failed (type mismatch) ",
              Util.pretty_unif ctxt tp'
            ]
            |> Pretty.string_of)
        in Seq.empty end
  in
    (@{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.block [
        Pretty.str "Higher-order unifying ",
        Util.pretty_unif ctxt (apply2 (Envir.norm_term env) tp)
      ]
      |> Pretty.string_of);
    unif ())
  end

end
