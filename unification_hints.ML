(*  Title:      E_Unification/unification_hints.ML
    Author:     Kevin Kappelmann, Paul Bachmann

Unification hints as introduced in "Hints in unification" by Asperti et al, 2009.
*)

signature UNIFICATION_HINTS =
sig
  include HAS_LOGGER

  val try_symmetric: bool Config.T
  structure Hints : NAMED_THMS

  type hint = (term * term) * ((indexname * typ) * term) list * thm
  val try_hints : Unification_Base.matcher -> Unification_Util.thm_normaliser
    -> Unification_Base.unifier -> hint list -> Unification_Base.unifier
  val gen_hint_list : Proof.context -> hint list
end

structure Unification_Hints : UNIFICATION_HINTS =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Unification_Hints"

structure Util = Unification_Util

structure Hints = Named_Thms(
  val name = @{binding "unif_hint"}
  val description = "Unification Hints"
)
val _ = Theory.setup Hints.setup

type hint = (term * term) * ((indexname * typ) * term) list * thm

val try_symmetric = Attrib.setup_config_bool @{binding "unification_hints_try_sym"} (K true)

fun pretty_hint ctxt (_, prems, thm) =
  let
    val pretty_prems =
      map (apply2 (Syntax.pretty_term ctxt) o apfst Var) prems
      |> map (fn (s1, s2) => Pretty.block [s1, Pretty.str " \<equiv> ", s2])
      |> Pretty.list "\<lbrakk>" "\<rbrakk>"
  in
    Pretty.block [
      pretty_prems,
      Pretty.str " \<Longrightarrow> ",
      Syntax.pretty_term ctxt (Thm.concl_of thm)
    ]
  end

fun incr_idx n = Logic.incr_indexes ([], [], n)

(*increase indexes in the premises of a hint*)
fun incr_indexes_prems n =
  map (fn (((s, i), T), t) => (((s, i + n), Logic.incr_tvar n T), incr_idx n t))

(*Tries to apply a hint to solve E-unification of (t1 \<equiv>? t2).
  Vars in hint are renamed to avoid naming conflicts during matching.
  Unifies the hint's pattern with (t1, t2) using match.
  Unifies resulting unification problems using unify.
  Normalises the theorems after unify with norm_thm_unif.
  Returns a sequence of (env, thm) pairs.
  Precondition: t1, t2 are normalised wrt the passed environment*)
fun try_hint try_symmetric match norm_thm_unif unify ctxt (t1, t2)
  (Envir.Envir {maxidx, tenv, tyenv})
  (hint as ((P_raw, Q_raw), hint_prems_raw, hint_thm_raw)) =
  let
    val _ = @{log Logger.TRACE} ctxt (fn _ =>
        Pretty.block [Pretty.str "Trying hint: ", pretty_hint ctxt hint]
        |> Pretty.string_of
      )

    (*increase indices to avoid naming conflicts*)
    val (P, Q) = apply2 (incr_idx (maxidx + 1)) (P_raw, Q_raw)
    val hint_prems = incr_indexes_prems (maxidx + 1) hint_prems_raw
    val hint_thm = Thm.incr_indexes (maxidx + 1) hint_thm_raw
    val maxidx_new = Thm.maxidx_of hint_thm
    val env' = Envir.Envir {maxidx=maxidx_new, tenv=tenv, tyenv=tyenv}

    (*match hint with unification pair, set flipped flag if symmetric hint matches*)
    val (no_hint_match, match_env_concl_thmpq) =
      let
        val match' = match ctxt
        fun match_hint tl tr =
          match' (P, tl) env'
          |> Seq.maps (fn (env'', thmL) => match' (Q, tr) env'' |> Seq.map (apsnd (pair thmL)))
        fun PQq _ = match_hint t1 t2 |> Seq.map (rpair false)
        fun QPq _ =
          if try_symmetric then match_hint t2 t1 |> Seq.map (rpair true)
          else Seq.empty
      in Seq.APPEND (PQq, QPq) () |> Util.seq_is_empty end
  in
    if no_hint_match then
      (@{log Logger.TRACE} ctxt (K "Hint does not match."); Seq.empty)
    else
      let
        val _ = @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
            Pretty.str "Hint ",
            pretty_hint ctxt hint,
            Pretty.str " matched. Unifying premises..."
          ]
          |> Pretty.string_of)

        (*unify each hint premise and collect the theorems while iteratively extending the environment*)
        fun unif_prem (v, s) = Seq.maps
          (fn (env, thms) => unify ctxt (Var v, s) env |> Seq.map (apsnd (fn thm => thm :: thms)))
        fun unify_prems ((match_env, concl_thmp), flipped) =
          fold unif_prem hint_prems (Seq.single (match_env, []))
          |> Seq.map (rpair (concl_thmp, flipped))

        fun inst_discharge ((env_res, prem_thms), (concl_thmp, flipped)) =
          let
            (*instantiate the theorems*)
            val norm_thm_unif = norm_thm_unif ctxt env_res
            val hint_thm_inst = norm_thm_unif hint_thm
            val prem_thms_inst = map norm_thm_unif prem_thms |> rev
            val (concl_thmL, concl_thmR) = apply2 norm_thm_unif concl_thmp
            (*discharge the hint premises; flip the theorem if needed*)
            val thm_res = Drule.implies_elim_list hint_thm_inst prem_thms_inst
              |> (fn thm => Unification_Base.transitive thm concl_thmR)
              |> Unification_Base.transitive (Unification_Base.symmetric concl_thmL)
              |> flipped ? Unification_Base.symmetric
          in (env_res, thm_res) end
      in
        Seq.maps unify_prems match_env_concl_thmpq
        |> Seq.map inst_discharge
      end
  end

(*try to apply every hint from the hint list*)
fun try_hints match norm_thm_unif unif hints ctxt (t1, t2) env =
  let val try_symmetric = Config.get ctxt try_symmetric
  in
    (@{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.block [Pretty.str "Trying unification hints for ",
        Util.pretty_unif ctxt (t1, t2)]
      |> Pretty.string_of);
    Seq.of_list hints
    |> Seq.maps (try_hint try_symmetric match norm_thm_unif unif ctxt (t1, t2) env))
  end

(*TODO: index hints in proper term index (cf. simplifier)*)
(* datatype unif_hints_set = Unif_Hints_Set of {hints : hint Net.net}

val empty_unif_hints_set = Unif_Hints_Set {hints = Net.empty}
val eq_ = Thm.eq_thm_prop (thm1, thm2)

fun merge_unif_hints_set uhs1 uhs2  =
  if pointer_eq (uhs1, uhs2) then uhs1
  else
    let
      val Unif_Hints_Set {hints = hints1} = uhs1;
      val Unif_Hints_Set {hints = hints2} = uhs2;
      val merged_hints = Net.merge eq_rrule (hints1, hints2);
    in Unif_Hints_Set {hints = merged_hints} end

structure Unif_Hints_Set = Generic_Data
(
  type T = unif_hints_set
  val empty = empty_unif_hints_set
  val extend = I
  val merge = merge_unif_hints_set
)

fun attrib f = Thm.declaration_attribute (map_ss o f);
val unif_hint_add = attrib undefined
val unif_hint_del = attrib undefined

val _ = Theory.setup (
  Attrib.setup @{binding unif_hint} (Attrib.add_del unif_hint_add unif_hint_del)
    "declaration of unification hint") *)

(*generates a hint from a theorem,
  returns (SOME hint,"") if successful,
  (NONE,thm_name) otherwise*)
fun gen_hint thm = (
    SOME
      (case Logic.dest_equals (Thm.concl_of thm) of
        (t1, t2) => (Envir.eta_contract t1, Envir.eta_contract t2),
      (Thm.prems_of thm
        |> map ((fn (Var x, t) => (x, Envir.eta_contract t)) o Logic.dest_equals)),
      Drule.eta_contraction_rule thm),
    ""
  )
  handle
    Match => (NONE, Thm.derivation_name thm)
  | TERM _ => (NONE, Thm.derivation_name thm)

(*generates a list of hints from named theorems "hints"*)
fun gen_hint_list ctxt =
  let
    val (hs, strs) = Hints.get ctxt
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
