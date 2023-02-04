(*  Title:      E_Unification/unify_resolve.ML
    Author:     Kevin Kappelmann

Resolution with parametrised unification function.
*)
signature UNIFY_RESOLVE =
sig
  structure Logger : LOGGER
  val CONCAT : tactic list -> tactic
  val CONCAT' : (int -> tactic) list -> int -> tactic

  val no_incr_biresolve_tac : Proof.context -> bool -> thm -> int -> tactic
  val no_incr_resolve_tac : Proof.context -> thm -> int -> tactic
  val no_incr_eresolve_tac : Proof.context -> thm -> int -> tactic

  val unify_resolve_tac : Unification_Util.thm_normaliser ->
    Unification_Base.unifier -> Proof.context -> thm -> int -> tactic
  val unify_resolve_tacs : Unification_Util.thm_normaliser ->
    Unification_Base.unifier -> Proof.context -> thm list -> (int -> tactic) list
  val unify_resolves_tac : Unification_Util.thm_normaliser ->
    Unification_Base.unifier -> Proof.context -> thm list -> int -> tactic
  val any_unify_resolve_tac : Unification_Util.thm_normaliser ->
    Unification_Base.unifier -> Proof.context -> thm list -> int -> tactic

end

structure Unify_Resolve : UNIFY_RESOLVE =
struct

structure Logger = @{new_logger "unif_resolve"}

structure Util = Unification_Util

fun CONCAT tacs = fold_rev (curry op APPEND) tacs no_tac
fun CONCAT' tacs = fold_rev (curry op APPEND') tacs (K no_tac)

fun no_incr_biresolve_tac ctxt eres rule =
  Thm.bicompose (SOME ctxt) {flatten = true, match = true, incremented = true}
  (eres, rule, Thm.nprems_of rule)

fun no_incr_resolve_tac ctxt = no_incr_biresolve_tac ctxt false

fun no_incr_eresolve_tac ctxt = no_incr_biresolve_tac ctxt true

fun unify_resolve_csubgoal_tac norm_thm unify ctxt rule (ct, i) st =
  let
    val t = Thm.term_of ct
    val rule = Thm.incr_indexes (Thm.maxidx_of_cterm ct + 1) rule
    val _ = @{log Logger.DEBUG} ctxt (fn _ =>
        Pretty.block [
          Pretty.str ("Calling unification resolution tactic on subgoal "),
          Pretty.str (Int.toString i),
          Pretty.str ": ",
          Util.pretty_terms ctxt [t],
          Pretty.str (" and rule "),
          Util.pretty_thm ctxt rule
        ]
        |> Pretty.string_of
      )
    val rule_concl = Thm.concl_of rule
    val concl = Logic.strip_imp_concl t
    val rule_concl_conclp = (rule_concl, concl)
    val env_thmsq = unify ctxt rule_concl_conclp (Util.empty_envir rule_concl_conclp)
    fun update_goal (env, unif_thm) =
      let
        fun rewrite_concl eq_thm thm =
          let
            val (lhs, rhs) = Thm.dest_equals (Thm.cconcl_of eq_thm)
            val eq_elim =
              Thm.instantiate' [] [SOME lhs, SOME rhs] Drule.equal_elim_rule1
          in
            Thm.implies_elim eq_elim eq_thm
            |> HEADGOAL (no_incr_resolve_tac ctxt thm)
          end
        val norm_thm = norm_thm ctxt env
        val inst_st = norm_thm st
        val inst_rule = norm_thm rule
        val inst_unif_thm = norm_thm unif_thm
        val _ = @{log Logger.DEBUG} ctxt (fn _ =>
            Pretty.block [
              Pretty.str ("Unification resolution tactic result on subgoal "),
              Pretty.str (Int.toString i),
              Pretty.str ": ",
              Util.pretty_thm ctxt inst_unif_thm
            ]
            |> Pretty.string_of
          )
        val rulesq = rewrite_concl inst_unif_thm inst_rule
        val updated_stsq =
          Seq.maps (fn rule => no_incr_resolve_tac ctxt rule i inst_st) rulesq
      in updated_stsq end
  in Seq.maps update_goal env_thmsq end

fun unify_resolve_tac norm_thm unify ctxt =
  CSUBGOAL o unify_resolve_csubgoal_tac norm_thm unify ctxt

fun unify_resolve_tacs norm_thm unify ctxt =
  map (unify_resolve_tac norm_thm unify ctxt)

fun unify_resolves_tac norm_thm unify ctxt =
  unify_resolve_tacs norm_thm unify ctxt #> EVERY'

fun any_unify_resolve_tac norm_thm unify ctxt =
  unify_resolve_tacs norm_thm unify ctxt #> CONCAT'


end
