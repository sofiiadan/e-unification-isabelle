structure Unification_Tests_Base =
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

fun thm_correct context unif tp =
  let
    val ctxt = Context.proof_of context
    (* val _ = writeln "unifying" *)
    (* val _ = apply2 (Pretty.writeln o Syntax.pretty_term ctxt) tp *)
    (* val _ = apply2 (Pretty.writeln o Syntax.pretty_typ ctxt o fastype_of) tp *)
    (* val _ = writeln "go" *)
    val (sigma, thm) = unif context tp (Unification_Util.empty_envir tp)
    (* val _ = writeln "now normalising" *)
    (* val _  = Unification_Util.pretty_env ctxt sigma |> Pretty.writeln *)
    val (t1, t2) = apply2 (Envir.norm_term sigma) tp
    val thm' = Unification_Util.norm_thm ctxt sigma thm
    (* val _ = writeln "done" *)
    val (lhs, rhs) = Thm.concl_of thm' |> Logic.dest_equals
    (* val _ = @{print} (lhs, rhs) *)
  in List.all Envir.aeconv [(t1, lhs), (t2, rhs)] end

fun show_termpair context =
  let
    val ctxt = Context.proof_of context
    val pretty_term = Syntax.pretty_term ctxt
  in SpecCheck_Show.zip pretty_term pretty_term end

val shrink_termpair = SpecCheck_Shrink.product SpecCheck_Shrink.term SpecCheck_Shrink.none

fun check gen name prop context =
  SpecCheck.check_shrink (show_termpair context) shrink_termpair 
    gen name prop (Context.proof_of context)

fun terms_unify unif context tp = can (unif context tp) (Unification_Util.empty_envir tp)

fun check_thm gen name unif context =
  check gen ("Theorem correctness: " ^ name)
    (SpecCheck_Property.==> (terms_unify unif context, thm_correct context unif))
    context

fun check_list tests name prop context =
  SpecCheck.check_list (show_termpair context) tests name prop (Context.proof_of context)

fun check_unit_tests_hints tests should_succeed hints name unif context r = 
  let val context' = fold (Named_Theorems.add_thm @{named_theorems "hints"}) hints context
  in 
    check_list tests ("unit tests for " ^ name)
      (SpecCheck_Property.prop
        (fn tp => the_default false (try (thm_correct context' unif) tp) = should_succeed))
      context'
    |> K r
  end

end
