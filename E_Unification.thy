\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>E-Unification\<close>
theory E_Unification
  imports Logging.Logging
begin

paragraph \<open>Summary\<close>
text \<open>Unification modulo equations.\<close>

ML_file\<open>unification_base.ML\<close>
ML_file\<open>util.ML\<close>

named_theorems hints
ML_file\<open>unification_hints.ML\<close>

ML_file\<open>first_order_unification.ML\<close>
ML_file\<open>higher_order_pattern_unification.ML\<close>

end
