theory First_Order_Tests
imports
  Unification_Tests_Base
begin

(*TODO: thm instantiation*)
ML_command\<open>
  structure Test_Params =
  struct
    open First_Order_Unification
    val params = {
      nv = 4,
      ni = 2,
      max_h = 5,
      max_args = 4
    }
  end
  structure First_Order_Tests = First_Order_Tests(Test_Params)
\<close>

ML\<open>
  structure Prop = SpecCheck_Property
  open Unification_Tests_Base
  val unify_hints = First_Order_Unification.unify_hints
  val unify = First_Order_Unification.unify
\<close>

(**** occurs-check ****)
ML_command\<open>
  let 
    val unit_tests = [
      (
        Var (("x", 0), TVar (("X", 0), [])),
        Var (("y", 0), TVar (("X", 0), []) --> TFree ("'a", [])) $
          Var (("x", 0), TVar (("X", 0), []))
      ),
      (
        Var (("y", 0), TVar (("X", 0), []) --> TFree ("'a", [])) $
          Var (("x", 0), TVar (("X", 0), [])),
        Var (("x", 0), TVar (("X", 0), []))
      ),
      (
        Free (("f", [TVar (("X", 0), []), TVar (("X", 0), [])] ---> TFree ("'a", []))) $
          Var (("x", 0), TVar (("X", 0), [])) $
          Var (("y", 0), TVar (("X", 0), [])),
        Free (("f", [TVar (("X", 0), []), TVar (("X", 0), [])] ---> TFree ("'a", []))) $
          Var (("y", 0), TVar (("X", 0), [])) $ (
            Free (("g", TVar (("X", 0), []) --> TVar (("X", 0), []))) $
              Var (("x", 0), TVar (("X", 0), []))
          )
      ),
      (
        Free (("f", [TVar (("X", 0), []), TVar (("Y", 0), [])] ---> TFree ("'a", []))) $
          Var (("x", 0), TVar (("X", 0), [])) $
          Var (("y", 0), TVar (("Y", 0), [])),
        Free (("f", [TVar (("Y", 0), []), TVar (("X", 0), [])] ---> TFree ("'a", []))) $
          Var (("y", 0), TVar (("Y", 0), [])) $ (
            Free (("g", TVar (("X", 0), []) --> TVar (("X", 0), []))) $
              Var (("x", 0), TVar (("X", 0), []))
          )
      )
    ]
    fun check name unif context _ = 
      check_list unit_tests ("occurs-check for " ^ name)
        (Prop.prop (not o can (thm_correct context unif))) context
      |> K ()
  in
    Lecker.test_group (Context.the_generic_context ()) () [
      check "unify" unify,
      check "unify_hints" unify_hints
    ]
  end
\<close>

end