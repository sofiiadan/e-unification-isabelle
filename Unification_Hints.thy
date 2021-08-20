theory Unification_Hints
imports
  Main
  Spec_Check2.Spec_Check
begin

ML_file\<open>logger.ML\<close>
ML_file\<open>utils.ML\<close>

named_theorems hints

ML_file\<open>unifier.ML\<close>
ML_file\<open>unification_hints.ML\<close>
ML_file\<open>first_order_unification.ML\<close>
ML_file "higher_order_pattern_unification.ML"

end
