(*  Title:      E_Unification/unification_hints.ML
    Author:     Kevin Kappelmann, Paul Bachmann

Unification hints as introduced in "Hints in unification" by Asperti et al, 2009.
*)

signature UNIFICATION_HINTS =
sig
  structure Logger : LOGGER

  type hint = (term * term) * ((indexname * typ) * term) list * thm
  val try_hints : Unification_Base.matcher -> Unification_Base.unifier -> hint list ->
    Unification_Base.unifier
  val gen_hint_list : Proof.context -> hint list
end

structure Unification_Hints : UNIFICATION_HINTS =
struct

structure Logger = @{new_logger "unification_hints"}

type hint = (term * term) * ((indexname * typ) * term) list * thm

fun pretty_hint ctxt (_, prems, thm) =
  let
    fun pretty_prems ctxt prems =
      map (apply2 (Syntax.pretty_term ctxt) o apfst Var) prems
      |> map (fn (s1, s2) => Pretty.block [s1, Pretty.str " \<equiv> ", s2])
      |> Pretty.list "\<lbrakk>" "\<rbrakk>"
  in
    Pretty.block [
      pretty_prems ctxt prems,
      Pretty.str " \<Longrightarrow> ",
      Syntax.pretty_term ctxt (Thm.concl_of thm)
    ]
  end

fun incr_idx n = Logic.incr_indexes ([], [], n)

(*increase indices in the premises of a hint*)
fun incr_indexes_prems n =
  map (fn (((s, i), T), t) => (((s, i + n), Logic.incr_tvar n T), incr_idx n t))

local
exception HINT_NO_MATCH
in

(*tries to apply a hint to solve E-unification of (t1\<equiv>?t2),
  Vars in hint are renamed to avoid naming conflicts during matching,
  matches the pattern with (t1,t2) using match,
  unifies resulting unification problems using unif,
  returns SOME (env,thm) if successfull,*)
fun try_hint match unif ctxt (t1, t2) (Envir.Envir {maxidx, tenv, tyenv})
  (hint as ((P_raw, Q_raw), hint_prems_raw, hint_thm_raw)) =
  let
    val _ = @{log Logger.TRACE} ctxt (fn _ =>
        Pretty.block [Pretty.str "Trying hint: ", pretty_hint ctxt hint]
        |> Pretty.string_of
      )

    (*increase indices o avoid naming conflicts*)
    val (P, Q) = apply2 (incr_idx (maxidx + 1)) (P_raw, Q_raw)
    val hint_prems = incr_indexes_prems (maxidx+1) hint_prems_raw
    val hint_thm = Thm.incr_indexes (maxidx + 1) hint_thm_raw
    val maxidx_new = Thm.maxidx_of hint_thm

    (*match hint with unification pair, set flip if hint matches flipped*)
    val ((match_tyenv, match_tenv), flip) =
      let
        val match' = match (Proof_Context.theory_of ctxt)
        val env = (tyenv, tenv)
      in
        (match' (P, t1) env |> match' (Q,t2), false)
        (*match against symmetric hint if first match fails*)
        handle Unification_Base.MATCH => (match' (Q,t1) env |> match' (P,t2), true)
          handle Unification_Base.MATCH => raise HINT_NO_MATCH
      end
    val match_env = Envir.Envir {tyenv=match_tyenv, tenv=match_tenv, maxidx=maxidx_new}

    val _ = @{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.block [Pretty.str "Hint ", pretty_hint ctxt hint,
        Pretty.str " matched. Unifying premises..."]
      |> Pretty.string_of)

    (*unify each hint premise and collect the theorems while iteratively extending the environment*)
    fun unif_prem (v, s) = Seq.maps
      (fn (env, thms) => unif ctxt (Var v, s) env |> Seq.map (apsnd (fn thm => thm :: thms)))
    val env_prem_thmsq = fold unif_prem hint_prems (Seq.single (match_env, []))

    fun inst_discharge (env_res, prem_thms) =
      let
        (*instantiate the theorems*)
        val norm_thm = Unification_Util.norm_thm ctxt env_res
        val prem_thms_inst = map norm_thm prem_thms |> rev
        val hint_thm_inst = norm_thm hint_thm
        (*discharge the hint premises; flip the theorem if needed*)
        val thm_res = Drule.implies_elim_list hint_thm_inst prem_thms_inst
          |> flip ? Unification_Base.symmetric
      in (env_res, thm_res) end
  in Seq.map inst_discharge env_prem_thmsq end
  handle
    HINT_NO_MATCH =>
      (@{log Logger.TRACE} ctxt (K "Hint does not match."); Seq.empty)

end

(*try to apply every hint from the hint list*)
fun try_hints match unif hints ctxt (t1, t2) env =
  (@{log Logger.DEBUG} ctxt (fn _ =>
    Pretty.block [Pretty.str "Trying unification hints for ",
      Unification_Util.pretty_terms ctxt [t1, t2]]
    |> Pretty.string_of);
  Seq.of_list hints
  |> Seq.maps (try_hint match unif ctxt (t1, t2) env))

(*generates a hint from a theorem,
  returns (SOME hint,"") if successful,
  (NONE,thm_name) otherwise*)
fun gen_hint thm = (
    SOME
      (case Logic.dest_equals (Thm.concl_of thm) of
        (t1,t2) => (Envir.eta_contract t1, Envir.eta_contract t2),
      (Thm.prems_of thm
        |> map ((fn (Var x,t) => (x, Envir.eta_contract t)) o Logic.dest_equals)),
      Drule.eta_contraction_rule thm),
    ""
  )
  handle
    Match => (NONE, Thm.derivation_name thm)
  | TERM _ => (NONE, Thm.derivation_name thm)

(*generates a list of hints from named theorems "hints"*)
fun gen_hint_list ctxt =
  let
    val (hs, strs) = Proof_Context.get_thms ctxt "hints"
      |> map gen_hint
      |> ListPair.unzip
    val thm_strs = filter (fn x => x <> "") strs
    val _ = if null thm_strs then ()
      else @{log} ctxt
        (fn _ => "These theorems cannot be used as hints: \n" ^ String.concatWith ", " thm_strs)
  in
    filter Option.isSome hs
    |> map Option.valOf
    |> rev
  end



end
