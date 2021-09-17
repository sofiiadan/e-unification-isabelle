\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Unification Test Setup\<close>
theory Unification_Tests_Base
imports
  Main
  Unification_Hints.Unification_Hints
  SpecCheck.SpecCheck
begin
paragraph \<open>Summary\<close>
text \<open>Shared setup for unification tests.\<close>

ML_file \<open>tests_base.ML\<close>
ML_file \<open>first_order_unification_tests.ML\<close>

end