\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Unification with Hints\<close>
theory Unification_Hints
imports
  Main
  SpecCheck.SpecCheck
begin
paragraph \<open>Summary\<close>
text \<open>Unification algorithms with hints.\<close>

ML_file\<open>logger.ML\<close>
ML_file\<open>unification_types.ML\<close>
ML_file\<open>util.ML\<close>

named_theorems hints

ML_file\<open>unification_hints.ML\<close>
ML_file\<open>first_order_unification.ML\<close>
ML_file "higher_order_pattern_unification.ML"

end
