\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>contributor "Paul Bachmann"\<close>
section \<open>First-Order Unification Tests\<close>
theory First_Order_Unification_Tests
imports
  Unification_Tests_Base
begin
paragraph \<open>Summary\<close>
text \<open>Tests for @{ML_structure "First_Order_Unification"}.\<close>

subsection \<open>Generated Tests\<close>
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
  structure First_Order_Tests = First_Order_Unification_Tests(Test_Params)
  val _ = First_Order_Tests.tests @{context} (SpecCheck_Random.new ())
\<close>

ML\<open>
  structure Prop = SpecCheck_Property
  open Unification_Tests_Base
  val unify_hints = First_Order_Unification.unify_hints
  val unify = First_Order_Unification.unify
\<close>

subsection \<open>Unit Tests\<close>
paragraph \<open>Occurs-Check\<close>
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
    fun check name unif ctxt _ =
      check_list unit_tests ("occurs-check for " ^ name)
        (Prop.prop (not o terms_unify_thms_correct ctxt unif)) ctxt
      |> K ()
  in
    Lecker.test_group @{context} () [
      check "unify" unify,
      check "unify_hints" unify_hints
    ]
  end
\<close>

paragraph \<open>Lambda-Abstractions\<close>
ML_command\<open>
  let
    val ctxt = Proof_Context.set_mode Proof_Context.mode_schematic @{context}
      |> Variable.declare_term @{term "f :: nat \<Rightarrow> bool \<Rightarrow> nat"}
    val hints = []
    val tests = map (apply2 (Syntax.read_term ctxt))[
      ("\<lambda> (x :: nat). (0 :: nat)", "\<lambda> (x :: nat). (0 :: nat)"),
      ("\<lambda> (x :: nat). x", "\<lambda> (x :: nat). x"),
      ("\<lambda> (x :: nat) (y :: bool). (x, y)", "\<lambda> (x :: nat) (y :: bool). (x, y)"),
      ("\<lambda> (x :: nat) (y :: bool). f x y", "\<lambda> (x :: nat) (y :: bool). (?x :: nat \<Rightarrow> bool \<Rightarrow> ?'Z) x y")
    ]
    val check_hints = check_unit_tests_hints tests
  in
    Lecker.test_group ctxt () [
      check_hints true [] "unify" unify,
      check_hints true [] "unify_hints without hints" unify_hints,
      check_hints true [] "unify_hints with hints" unify_hints
    ]
  end
\<close>

ML_command\<open>
  let
    val ctxt = Proof_Context.set_mode Proof_Context.mode_schematic @{context}
      |> Variable.declare_term @{term "f :: nat \<Rightarrow> bool \<Rightarrow> nat"}
    val hints = map (Skip_Proof.make_thm (Proof_Context.theory_of ctxt) o Syntax.read_term ctxt) [
      "?x \<equiv> (0 :: nat) \<Longrightarrow> ?y \<equiv> ?z \<Longrightarrow> ?x + ?y \<equiv> ?z"
    ]
    val tests = map (apply2 (Syntax.read_term ctxt))[
      ("\<lambda> (x :: nat) (y :: bool). x", "\<lambda> (x :: nat) (y :: bool). 0 + x"),
      ("0 + (\<lambda> (x :: nat) (y :: bool). x) 0 ?y", "0 + (\<lambda> (x :: nat) (y :: bool). 0 + x) 0 ?z")
    ]
    val check_hints = check_unit_tests_hints tests
  in
    Lecker.test_group ctxt () [
      check_hints false [] "unify" unify,
      check_hints false [] "unify_hints without hints" unify_hints,
      check_hints true hints "unify_hints with hints" unify_hints
    ]
  end
\<close>

end
