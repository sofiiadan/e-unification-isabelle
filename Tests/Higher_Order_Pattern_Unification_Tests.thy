\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>contributor "Paul Bachmann"\<close>
section \<open>Higher-Order Pattern Unification Tests\<close>
theory Higher_Order_Pattern_Unification_Tests
imports
  Unification_Tests_Base
begin
paragraph \<open>Summary\<close>
text \<open>Tests for @{ML_structure "Higher_Order_Pattern_Unification"}.\<close>
(* declare[[show_types]] *)
(* config[Higher_Order_Pattern_Unification.Logger.log_level_config=600] *)
(* config[Unification_Hints.Logger.log_level_config=1000] *)
subsection \<open>Generated Tests\<close>
ML_command\<open>
  structure Test_Params =
  struct
    open Higher_Order_Pattern_Unification
    val params = {
      nv = 10,
      ni = 10,
      max_h = 5,
      max_args = 4
    }
  end
  structure First_Order_Tests = First_Order_Unification_Tests(Test_Params)
  val _ = First_Order_Tests.tests (Context.the_generic_context ()) (SpecCheck_Random.new ())
\<close>

subsection \<open>Unit Tests\<close>
ML\<open>
  open Unification_Tests_Base
  val unify_hints = Higher_Order_Pattern_Unification.unify_hints
  val unify = Higher_Order_Pattern_Unification.unify
\<close>

paragraph \<open>Standard Unification\<close>
ML_command\<open>
  let
    val ctxt = Proof_Context.set_mode Proof_Context.mode_schematic @{context}
    val context = Context.Proof ctxt
    val tests = map (apply2 (Syntax.read_term ctxt)) [
      ("\<lambda> x. f x", "\<lambda> x. f x"),
      ("\<lambda> (x :: ?'X). (f :: ?'X \<Rightarrow> ?'Y) x", "\<lambda> (x :: ?'X1). (?y :: ?'X1 \<Rightarrow> ?'Y1) x"),
      ("\<lambda> x. r x ?X", "\<lambda> x. r x ?Y"),
      ("\<lambda> x. (x, (\<lambda> y. (y, \<lambda> z. ?x)))", "\<lambda> x. (x, (\<lambda> y. (y, \<lambda> z. g)))"),
      ("?f :: ?'Z \<Rightarrow> ?'X \<Rightarrow> ?'Y \<Rightarrow> ?'R", "\<lambda> (x :: ?'Z). (?f :: ?'Z \<Rightarrow> ?'X1 \<Rightarrow> ?'Y1 \<Rightarrow> ?'R1) x"),
      (
        "(?x :: ?'X, ?y :: ?'Y, ?z :: ?'Z)",
        "((f :: ?'Y \<Rightarrow> ?'X) (?y :: ?'Y), (g :: ?'Z \<Rightarrow> ?'Y) (?z :: ?'Z), c :: ?'C)"
      )
   ]
    val check_hints = check_unit_tests_hints tests
  in
    Lecker.test_group context () [
      check_hints true [] "unify" unify,
      check_hints true [] "unify_hints without hints" unify_hints,
      check_hints true [] "unify_hints with hints" unify_hints
    ]
  end
\<close>

paragraph \<open>With Unification Hints\<close>
ML_command\<open>
  let
    val ctxt = Proof_Context.set_mode Proof_Context.mode_schematic @{context}
      |> Variable.declare_term @{term "f :: (nat \<Rightarrow> nat) \<times> nat \<Rightarrow> nat"}
      |> Variable.declare_term @{term "g :: nat \<times> nat \<Rightarrow> nat"}
      |> Variable.declare_term @{term "h :: nat"}
    val context = Context.Proof ctxt
    val hints = map (Skip_Proof.make_thm (Context.theory_of context) o Syntax.read_term ctxt) [
      "?x \<equiv> (0 :: nat) \<Longrightarrow> ?y \<equiv> ?z \<Longrightarrow> ?x + ?y \<equiv> ?z",
      "(?x :: ?'X) \<equiv> (?y :: ?'X) \<Longrightarrow> id ?x \<equiv> ?y",
      "(?x1 :: nat) \<equiv> ?x2 \<Longrightarrow> (?y1 :: nat) \<equiv> ?y2 \<Longrightarrow> ?x1 + ?y1 \<equiv> ?y2 + ?x2"
    ]
    val tests = map (apply2 (Syntax.read_term ctxt)) [
      ("\<lambda> x y. 0 + 1 :: nat", "\<lambda> x y. 1 :: nat"),
      ("\<lambda> x. 0 + 0 + x :: nat", "\<lambda> x. x :: nat"),
      ("\<lambda> x y. 0 + Suc ?x", "\<lambda> x y. Suc 2"),
      ("\<lambda> (x :: nat) (y :: nat). y + (0 + x)", "\<lambda> (x :: nat) (y :: nat). x + (0 + y)"),
      ("f (\<lambda> u. g (?x, h), h)", "id (f (\<lambda> u. ?y, 0 + h))")
   ]
    val check_hints = check_unit_tests_hints tests
  in
    Lecker.test_group context () [
      check_hints false [] "unify" unify,
      check_hints false [] "unify_hints without hints" unify_hints,
      check_hints true hints "unify_hints with hints" unify_hints
    ]
  end
\<close>

end
