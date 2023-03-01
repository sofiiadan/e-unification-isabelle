\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Higher-Order Unification Tests\<close>
theory Higher_Order_Unification_Tests
imports
  Unification_Tests_Base
begin

paragraph \<open>Summary\<close>
text \<open>Tests for @{ML_structure "Higher_Order_Unification"}.\<close>

ML\<open>
  structure Prop = SpecCheck_Property
  open Unification_Tests_Base
  structure Unif = Higher_Order_Unification
  val unify = Unif.unify
\<close>

subsection \<open>Unification\<close>
subsubsection \<open>Generated Tests\<close>

paragraph \<open>First Order\<close>

ML_command\<open>
  structure Test_Params =
  struct
    open Unif
    (*Note: there is no higher-order unification with hints as of now;
      we hence use the higher-order pattern hints unifier for those tests*)
    val unify_hints = Higher_Order_Pattern_Unification.unify_hints
    val params = {
      nv = 10,
      ni = 10,
      max_h = 5,
      max_args = 4
    }
  end
  structure First_Order_Tests = First_Order_Unification_Tests(Test_Params)
  val _ = First_Order_Tests.tests @{context} (SpecCheck_Random.new ())
\<close>

paragraph \<open>Higher Order\<close>

ML_file\<open>higher_order_pattern_unification_tests.ML\<close>

ML_command\<open>
  structure Tests = Higher_Order_Pattern_Unification_Tests(Unif)
  val ctxt = Proof_Context.set_mode Proof_Context.mode_schematic @{context}
  val tests = Tests.unit_tests_unifiable ctxt
  val check_hints = check_unit_tests_hints_unif tests
  val _ = Lecker.test_group ctxt () [
      check_hints true [] "unify" unify
    ]
\<close>

subsubsection \<open>Unit Tests\<close>

ML_command\<open>
  let
    val ctxt = Proof_Context.set_mode Proof_Context.mode_schematic @{context}
    val tests = map (apply2 (Syntax.read_term ctxt)) [
      ("?X ?Y", "?Y ?Z"),
      ("?X ?Y (?K ?M)", "f c (?L ?N)")
   ]
    val check_hints = check_unit_tests_hints_unif tests
  in
    Lecker.test_group ctxt () [
      check_hints true [] "unify" unify
    ]
  end
\<close>

end
