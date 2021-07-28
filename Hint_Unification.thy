theory Hint_Unification
imports
  Main
  Spec_Check2.Spec_Check
begin

ML_file\<open>Log.ML\<close>
ML_file\<open>Utils.ML\<close>

named_theorems hints

ML_file\<open>Hint_Unification.ML\<close>
ML_file\<open>FO_Hint_Unification.ML\<close>
ML_file "HO_Pat_Hint_Unification.ML"


end
