(*  Title:      E_Unification/unify_resolve.ML
    Author:     Kevin Kappelmann

Resolution with parametrised unification function.
*)
signature UNIFY_RESOLVE =
sig
  structure Logger : LOGGER
  val CONCAT : tactic list -> tactic
  val CONCAT' : (int -> tactic) list -> int -> tactic

  val no_lift_biresolve_tac : Proof.context -> bool -> thm -> int -> tactic
  val no_lift_resolve_tac : Proof.context -> thm -> int -> tactic
  val no_lift_eresolve_tac : Proof.context -> thm -> int -> tactic

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

structure Logger = @{new_logger "unify_resolve"}

structure Util = Unification_Util

fun CONCAT tacs = fold_rev (curry op APPEND) tacs no_tac
fun CONCAT' tacs = fold_rev (curry op APPEND') tacs (K no_tac)

fun no_lift_biresolve_tac ctxt eres rule =
  Thm.bicompose (SOME ctxt) {flatten = true, match = true, incremented = true}
  (eres, rule, Thm.nprems_of rule)

fun no_lift_resolve_tac ctxt = no_lift_biresolve_tac ctxt false

fun no_lift_eresolve_tac ctxt = no_lift_biresolve_tac ctxt true

fun unify_resolve_csubgoal_tac norm_thm unify ctxt rule (cgoal, i) state =
  let
    val rule = Thm.incr_indexes (Thm.maxidx_of_cterm cgoal + 1) rule
    (*fix parameters of goal*)
    val ((goal_params, cgoal_focused), ctxt') = Variable.focus_cterm NONE cgoal ctxt
      |>> apfst (map snd)
    val goal_focused = Thm.term_of cgoal_focused
    val _ = @{log Logger.DEBUG} ctxt (fn _ =>
        Pretty.block [
          Pretty.str ("Calling unification resolution tactic on subgoal "),
          Pretty.str (Int.toString i),
          Pretty.str ": ",
          Util.pretty_terms ctxt' [goal_focused],
          Pretty.str (" and rule "),
          Util.pretty_thm ctxt' rule
        ]
        |> Pretty.string_of
      )
    val rule_concl = Thm.concl_of rule
    val goal_concl = Logic.strip_assums_concl goal_focused
    val conclp = (rule_concl, goal_concl)
    val env_thmsq = unify ctxt' conclp (Util.empty_envir conclp)
    fun update_goal (env, unif_thm) =
      let
        (*normalise all components wrt. env*)
        val norm_thm_inst = norm_thm ctxt' env
        val inst_state = norm_thm_inst state
        val inst_cgoal = Thm.cprem_of inst_state i
        val norm_goal_param = Thm.reflexive
          #> norm_thm_inst
          #> Thm.cprop_of
          #> Thm.dest_equals_rhs
        val inst_goal_params = map norm_goal_param goal_params
        val inst_rule = norm_thm_inst rule
        val inst_unif_thm = norm_thm_inst unif_thm
        val _ = @{log Logger.DEBUG} ctxt' (fn _ =>
            Pretty.block [
              Pretty.str ("Unification resolution tactic result on subgoal "),
              Pretty.str (Int.toString i),
              Pretty.str ": ",
              Util.pretty_thm ctxt' inst_unif_thm
            ]
            |> Pretty.string_of
          )
        fun rewrite_rule eq_thm rule =
          let
            val (lhs, rhs) = Thm.dest_equals (Thm.cconcl_of eq_thm)
            val eq_elim =
              Thm.instantiate' [] [SOME lhs, SOME rhs] Drule.equal_elim_rule1
          in
            Thm.implies_elim eq_elim eq_thm
            |> HEADGOAL (no_lift_resolve_tac ctxt' rule)
          end
        fun lift_rule rule =
          let
            val maxidx_inst_goal = Thm.maxidx_of_cterm inst_cgoal
            val inst_goal_paramTs = map Thm.typ_of_cterm inst_goal_params
            val (goal_param_vars, maxidx_params) =
              Util.fresh_vars "p" inst_goal_paramTs maxidx_inst_goal
            val num_goal_params = maxidx_params - maxidx_inst_goal
            val cgoal_param_vars = map (Thm.cterm_of ctxt') goal_param_vars
            val rule =
              (*abstract parameters*)
              Drule.forall_intr_list inst_goal_params rule
              (*instantiate meta variables*)
              |> Drule.forall_elim_list cgoal_param_vars
              (*lift*)
              |> Thm.lift_rule inst_cgoal
            (*lifting the rule shifts the indexes of variables*)
            val idx_lift_offset = maxidx_inst_goal + 1
            (*computes the index of a variable before it was lifted*)
            fun comp_old_idx idx = idx - idx_lift_offset
            (*checks whether a variable corresponds to a goal parameter,
              as identified by the unifier*)
            val is_goal_param =
              let val adjusted_goal_param_names =
                map (fn Var ((n, idx), _) => (n, idx + idx_lift_offset)) goal_param_vars
              in member Term.eq_ix adjusted_goal_param_names end
            (*compute the substitutions*)
            val rule_tvars = build (Term.add_tvars (Thm.prop_of rule))
            fun adjust_tvar (var as ((n, idx), s)) acc =
              if idx <= maxidx_inst_goal then acc
              else
                let val cvar = TVar ((n, comp_old_idx idx), s) |> Thm.ctyp_of ctxt
                in TVars.add (var, cvar) acc end
            val inst_tvars = fold adjust_tvar rule_tvars TVars.empty
            val rule_vars = build (Term.add_vars (Thm.prop_of rule))
            fun mk_abs [] body = body
              | mk_abs (T :: Ts) body = Abs ("", T, mk_abs Ts body)
            fun add_abstractions (name as (n, idx), T) acc =
              if idx <= maxidx_inst_goal then acc
              else
                let
                  val body = if is_goal_param name
                    (*project to the correct, newly bound parameter*)
                    then Bound (num_goal_params - 1 - (idx - 2 * idx_lift_offset))
                    (*ignore the newly introduced parameters*)
                    else
                      let val smallerT = strip_type T
                        |>> drop num_goal_params
                        |> (op --->)
                      in Var ((n, comp_old_idx idx), smallerT) end
                  val cabs = mk_abs inst_goal_paramTs body
                    |> Thm.cterm_of ctxt
                    |> Thm.instantiate_cterm (inst_tvars, Vars.empty)
                in Vars.add ((name, Thm.typ_of_cterm cabs), cabs) acc end
            val inst_vars = fold add_abstractions rule_vars Vars.empty
            val rule = Thm.instantiate (inst_tvars, inst_vars) rule
              (*we must not forget to normalise since we may have created redexes*)
              |> norm_thm ctxt Envir.init
          in rule end
        val rulesq = rewrite_rule inst_unif_thm inst_rule |> Seq.map lift_rule
        val updated_statesq =
          Seq.maps (fn rule => no_lift_resolve_tac ctxt rule i inst_state) rulesq
      in updated_statesq end
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
