signature UNIFICATION_TESTS_BASE =
sig

  val term_gen : Proof.context -> int -> int -> int * int * int * int ->
    (int -> int -> int SpecCheck_Generator.gen) -> term SpecCheck_Generator.gen
  val term_pair_gen : Proof.context -> int -> int -> int * int * int * int ->
    (int -> int -> int SpecCheck_Generator.gen) ->
    (term * term) SpecCheck_Generator.gen

  val term_gen' : Proof.context -> int -> int -> int * int * int * int -> int ->
    int -> term SpecCheck_Generator.gen
  val term_pair_gen' : Proof.context -> int -> int -> int * int * int * int ->
    int -> int -> (term * term) SpecCheck_Generator.gen

  val thms_correct : Proof.context -> Unification_Base.unifier ->
    (term * term) SpecCheck_Property.pred

  val terms_unify : Proof.context -> Unification_Base.unifier ->
    (term * term) SpecCheck_Property.pred

  val terms_unify_thms_correct : Proof.context -> Unification_Base.unifier ->
    (term * term) SpecCheck_Property.pred

  val add_hints : thm list -> Proof.context -> Proof.context

  val check : (term * term, 'a) SpecCheck_Generator.gen_state -> string ->
    (term * term) SpecCheck_Property.prop ->
    (Proof.context, 'a) Lecker.test_state

  val check_thm : (term * term, 'a) SpecCheck_Generator.gen_state -> string ->
    Unification_Base.unifier -> (Proof.context, 'a) Lecker.test_state

  val check_list : (term * term) list -> string ->
    (term * term) SpecCheck_Property.prop -> Proof.context ->
    (term * term) Seq.seq

  val check_unit_tests_hints : (term * term) list -> bool -> thm list ->
    string -> Unification_Base.unifier ->
    (Proof.context, 'a) Lecker.test_state

end

structure Unification_Tests_Base : UNIFICATION_TESTS_BASE =
struct

structure Gen = SpecCheck_Generator

fun term_num_args_gen nv ni weights num_args_gen h i =
  Gen.zip (Gen.aterm' (Gen.nonneg nv) (Gen.nonneg ni) weights) (num_args_gen h i)

fun term_gen ctxt nv ni weights num_args_gen =
  let val ctxt' = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
  in
    Gen.term_tree (term_num_args_gen nv ni weights num_args_gen)
    |> Gen.map (try (singleton (Variable.polymorphic ctxt') o Syntax.check_term ctxt'))
    |> Gen.filter is_some
    |> Gen.map the
  end

fun term_pair_gen ctxt nv ni weights num_args_gen =
  let
    val ctxt' = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
    val term_gen = Gen.term_tree (term_num_args_gen nv ni weights num_args_gen)
  in
    Gen.zip term_gen term_gen
    |> Gen.map (fn (s, t) => try (Variable.polymorphic ctxt' o Syntax.check_terms ctxt') [s, t])
    |> Gen.filter is_some
    |> Gen.map (fn SOME [s, t] => (s, t))
  end

fun num_args_gen max_h max_args h _ = if h > max_h then Gen.return 0 else Gen.nonneg max_args

fun term_gen' ctxt nv ni weights max_h max_args =
  term_gen ctxt nv ni weights (num_args_gen max_h max_args)

fun term_pair_gen' ctxt nv ni weights max_h max_args =
  term_pair_gen ctxt nv ni weights (num_args_gen max_h max_args)

fun show_termpair ctxt =
  let val pretty_term = Syntax.pretty_term ctxt
  in SpecCheck_Show.zip pretty_term pretty_term end

val shrink_termpair = SpecCheck_Shrink.product SpecCheck_Shrink.term SpecCheck_Shrink.none

fun thms_correct ctxt unif tp =
  let
    val env_thmq = unif ctxt tp (Unification_Util.empty_envir tp)
    fun thm_correct (env, thm) =
      let
        val (t1, t2) = apply2 (Envir.norm_term env) tp
        val thm' = Unification_Util.norm_thm ctxt env thm
        val (lhs, rhs) = Thm.concl_of thm' |> Logic.dest_equals
      in List.all Envir.aeconv [(t1, lhs), (t2, rhs)] end
  in List.all thm_correct (Seq.list_of env_thmq) end

fun terms_unify ctxt unif tp =
  Unification_Util.empty_envir tp
  |> unif ctxt tp
  |> Unification_Util.seq_is_empty
  |> not
  handle Unification_Base.PATTERN => false

fun terms_unify_thms_correct ctxt unif tp =
  terms_unify ctxt unif tp andalso thms_correct ctxt unif tp

fun check gen name prop ctxt =
  SpecCheck.check_shrink (show_termpair ctxt) shrink_termpair
    gen name prop ctxt

fun check_thm gen name unif ctxt = check gen ("Theorem correctness: " ^ name)
  (SpecCheck_Property.==> (terms_unify ctxt unif, thms_correct ctxt unif))
  ctxt

fun check_list tests name prop ctxt =
  SpecCheck.check_list (show_termpair ctxt) tests name prop ctxt

fun add_hints thms ctxt =
  fold (Named_Theorems.add_thm @{named_theorems "hints"}) thms (Context.Proof ctxt)
  |> Context.proof_of

fun check_unit_tests_hints tests should_succeed hints name unif ctxt s =
  let val ctxt' = add_hints hints ctxt
  in
    check_list tests name
      (SpecCheck_Property.prop
        (fn tp => terms_unify_thms_correct ctxt' unif tp = should_succeed))
      ctxt'
    |> K s
  end

end
