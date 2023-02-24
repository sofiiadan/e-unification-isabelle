\<^marker>\<open>creator "Sofiia Danylchenko"\<close>
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
  val unify = Higher_Order_Unification.unify
  val hounify = Higher_Order_Unification.hounify
\<close>

(*
config[First_Order_Unification.Logger.log_level=1000]
config[Higher_Order_Unification.Logger.log_level=1000]
config[Higher_Order_Pattern_Unification.Logger.log_level=1000]
config[Unification_Hints.Logger.log_level=1000]
config[Root_Logger.log_level=1000]
config[show_types=true]
config[eta_contract=false]
config[Logging_Antiquotations.show_pos=false]
*)

(*TODO: rewrite to satisfy HO unification*)

ML_command\<open>\<close>

end
