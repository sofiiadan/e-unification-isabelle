\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>E-Unification\<close>
theory E_Unification
  imports Logging.Logging
begin

paragraph \<open>Summary\<close>
text \<open>Unification modulo equations.\<close>

text \<open>Basics\<close>
ML_file\<open>unification_base.ML\<close>
ML_file\<open>util.ML\<close>

text \<open>Resolution with unification\<close>
ML_file\<open>unif_resolve.ML\<close>

text \<open>Unification hints\<close>
ML_file\<open>unification_hints.ML\<close>

text \<open>Unifiers\<close>
ML_file\<open>higher_order_unification.ML\<close>
ML_file\<open>higher_order_pattern_unification.ML\<close>
ML_file\<open>first_order_unification.ML\<close>


end
