(*  Title:      Unification_Hints/unification_hints.ML
    Author:     Kevin Kappelmann, Paul Bachmann

Unification hints as introduced in "Hints in unification" by Asperti et al, 2009.
*)
signature UNIFICATION_HINTS =
sig

  type hint = (term * term) * ((indexname * typ) * term) list * thm

  val reflexive : cterm -> thm
  val combination : thm -> thm -> thm
  val symmetric : thm -> thm
  val abstract_rule : string -> cterm -> thm -> thm

  val reflexive_term : Context.generic -> term -> thm

  val gen_hint_list : Proof.context -> hint list

  val try_hints : Context.generic -> Unification_Types.matcher -> Unification_Types.unifier ->
    hint list -> Envir.env -> term * term -> (Envir.env * thm) Seq.seq

end

structure Unification_Hints : UNIFICATION_HINTS =
struct

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

val reflexive = Thm.reflexive
val combination = Thm.combination
val symmetric = Thm.symmetric
val abstract_rule = Thm.abstract_rule

fun reflexive_term context t = reflexive (Thm.cterm_of (Context.proof_of context) t)

fun incr_idx n = Logic.incr_indexes ([], [], n)

(*increase indices in the premises of a hint*)
fun incr_indexes_prems n =
  map (fn (((s, i), T), t) => (((s, i + n), Logic.incr_tvar n T), incr_idx n t))

(*generates a hint from a theorem,
  returns (SOME hint,"") if successful,
  (NONE,thm_name) otherwise*)
fun gen_hint thm = (SOME
  (case Logic.dest_equals (Thm.concl_of thm) of
     (t1,t2) => (Envir.eta_contract t1,Envir.eta_contract t2),
  (Thm.prems_of thm
     |> map ((fn (Var x,t) => (x,Envir.eta_contract t)) o Logic.dest_equals)),
    Drule.eta_contraction_rule thm),"")
  handle
    Match => (NONE,Thm.derivation_name thm)
  | TERM _ => (NONE,Thm.derivation_name thm)

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
        Logger.info ctxt tracing
          ("These theorems cannot be used as hints: \n"^ String.concatWith ", " thm_strs)
  in
    hs |> filter Option.isSome
       |> map Option.valOf
       |> rev
  end

(*tries to apply a hint to solve E-unification of (t1\<equiv>?t2),
  Vars in hint are renamed to avoid naming conflicts during matching,
  matches the pattern with (t1,t2) using match,
  unifies resulting unification problems using unif,
  returns SOME (env,thm) if successfull,*)
fun try_hint context match unif (Envir.Envir {maxidx, tenv, tyenv}) (t1, t2)
  (hint as ((P_raw, Q_raw), hint_prems_raw, hint_thm_raw)) =
  let
    val ctxt = Context.proof_of context
    val _ = Logger.trace ctxt
      (fn _ =>
        Pretty.block [Pretty.str "Trying hint: ", pretty_hint ctxt hint]
        |> Pretty.string_of
        |> tracing)
      ()

    (*increase indices o avoid naming conflicts*)
    val (P, Q) = apply2 (incr_idx (maxidx + 1)) (P_raw, Q_raw)
    val hint_prems = incr_indexes_prems (maxidx+1) hint_prems_raw
    val hint_thm = Thm.incr_indexes (maxidx + 1) hint_thm_raw
    val maxidx_new = Thm.maxidx_of hint_thm

    (*match hint with unification pair, set flip if hint matches flipped*)
    val ((match_tyenv, match_tenv), flip) =
      let
        val match' = match (Context.theory_of context)
        val env = (tyenv, tenv)
      in
        (match' (P, t1) env |> match' (Q,t2), false)
        (*match against symmetric hint if first match fails*)
        (*TODO: uncomment*)
        (* handle Unification_Types.MATCH => (match' (Q,t1) env |> match' (P,t2), true) *)
        handle Pattern.MATCH => (match' (Q,t1) env |> match' (P,t2), true)
      end
    val match_env = Envir.Envir {tyenv=match_tyenv, tenv=match_tenv, maxidx=maxidx_new}

    val _ = Logger.debug ctxt
      (fn _ =>
        Pretty.block [Pretty.str "Hint ", pretty_hint ctxt hint,
          Pretty.str " matched. Unifying premises..."]
        |> Pretty.writeln)
      ()

    (*unify each hint premise and collect the theorems while iteratively
      extending the environment*)
    fun prem_unif (v, s) (env, thms) = unif context (Var v, s) env ||> (fn thm => thm :: thms)
    val (env_res, prem_env_thms) = fold prem_unif hint_prems (match_env, [])

    (*instantiate the theorems*)
    val prem_env_thms_inst = map (Unification_Util.norm_thm ctxt env_res) prem_env_thms |> rev
    val thm_inst = Unification_Util.norm_thm ctxt env_res hint_thm
    (*discharge the hint premises; flip the theorem if needed*)
    val thm_res = Drule.implies_elim_list thm_inst prem_env_thms_inst
      |> (if flip then symmetric else I)
  in
    Logger.debug ctxt
      (fn _ =>
        Pretty.block [Pretty.str "All premises unified; resulting theorem: ",
          Unification_Util.pretty_thm ctxt thm_res]
        |> Pretty.writeln)
      ();
    SOME (env_res, thm_res)
  end
    handle
      (*TODO: uncomment*)
      (* Unification_Types.MATCH =>
        (Logger.trace (Context.proof_of context) tracing "Hint does not match"; NONE) *)
      Pattern.MATCH => (Logger.trace (Context.proof_of context) tracing "Hint does not match"; NONE)
    | exn => if Exn.is_interrupt exn then Exn.reraise exn else 
        (Logger.debug (Context.proof_of context) writeln "Hint matches but cannot unify premises";
        NONE)

(*try to apply every hint from the hint list*)
fun try_hints context match unif hints envir (t1,t2) =
  let val ctxt = Context.proof_of context
  in
    Logger.debug ctxt
      (fn _ =>
        Pretty.block [Pretty.str "Trying unification hints for ",
          Unification_Util.pretty_terms ctxt [t1, t2]]
        |> Pretty.writeln)
      ();
    Seq.of_list hints
    |> Seq.map_filter (try_hint context match unif envir (t1,t2))
  end

end
