\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>contributor "Paul Bachmann"\<close>
section \<open>Examples\<close>
theory Unification_Hints_Examples
imports
  Complex_Main
  E_Unification.E_Unification
begin
paragraph \<open>Summary\<close>
text \<open>Sample applications of unification hints.\<close>

ML\<open>
  val _ = Theory.setup (
    ML_Antiquotation.inline_embedded \<^binding>\<open>term_pat\<close>
    (Args.term_pattern >> (ML_Syntax.atomic o ML_Syntax.print_term)))
\<close>

(* ML\<open>
  val (s, t) = (
      @{term_pat "\<lambda> (x :: ?'X1) (y :: ?'Y1) (z :: ?'Z1). (?a :: ?'Z1 \<Rightarrow> ?'X1 \<Rightarrow> ?'Y1 \<Rightarrow> ?'R1) z x y"},
      @{term_pat "\<lambda> (x :: ?'X2) (y :: ?'Y2) (z :: ?'Z2). (?b :: ?'Y2 \<Rightarrow> ?'X2 \<Rightarrow> ?'Z2 \<Rightarrow> ?'R2) y x"}
      (* @{term_pat "?a :: ?'Z1 \<Rightarrow> ?'X1 \<Rightarrow> ?'Y1 \<Rightarrow> ?'R1"},
      @{term_pat "\<lambda> (x :: ?'X2). (?a :: ?'X2 \<Rightarrow> ?'Y2 \<Rightarrow> ?'Z2 \<Rightarrow> ?'R2) x"} *)
      (* @{term_pat "(?x :: ?'X, ?y :: ?'Y, ?z :: ?'Z)"},
      @{term_pat "((f :: ?'Y \<Rightarrow> ?'X) (?y :: ?'Y), (g :: ?'Z \<Rightarrow> ?'Y) (?z :: ?'Z), c :: ?'C)"} *)
      (* @{term_pat "(?y :: ?'Y, ?y :: ?'Y, ?z :: ?'Z)"},
      @{term_pat "(?x :: ?'X, ?z :: ?'Z, ?c :: ?'C)"} *)
      (* @{term_pat "(?z :: ?'Z, ?y :: ?'Y, ?x :: ?'X)"}, *)
      (* @{term_pat "(?y :: ?'Y, ?x :: ?'X, ?c :: ?'C)"} *)
    )
  val env = Higher_Order_Pattern_Unification.unify (Context.the_generic_context ()) (t, s)
      (Unification_Util.empty_envir (s, t))
  val _ = Unification_Util.pretty_env @{context} (fst env) |> Pretty.writeln
  val _ = Unification_Util.norm_thm @{context} (fst env) (snd env)
\<close> *)

(* ML\<open>
  (*Pattern unifier does not unify types correctly*)
  val (t, s) = (
      @{term_pat "(?x :: ?'X \<Rightarrow> ?'R)"},
      @{term_pat "(?y :: ?'Y \<Rightarrow> ?'R)"}
    )
  val env =
    Unify.unifiers ((Context.the_generic_context ()), Envir.empty 0, [(t,s)]) |> Seq.hd
  val _ =
    Unify.smash_unifiers (Context.the_generic_context ()) [(t,s)] (Envir.empty 0)
    |> Seq.hd
    |> Unification_Util.pretty_env @{context}
    |> Pretty.writeln
\<close> *)

ML\<open>
  structure Util = Unification_Util
  val unify = Higher_Order_Pattern_Unification.unify_hints
\<close>

subsection \<open>Reflexive Tactics\<close>

subsubsection \<open>Simple Arithmetic\<close>
datatype Expr = Var int | Add Expr Expr

fun eval :: "Expr \<Rightarrow> int" where
  "eval (Var i) = i"
| "eval (Add ex1 ex2) = eval ex1 + eval ex2"

consts simpl :: "Expr \<Rightarrow> Expr"

(* lemma soundness : "P (eval (simpl e)) \<Longrightarrow> P (eval e)" sorry *)

(*supply base case and inductive hint*)
lemma eval_Var [hints]: "e \<equiv> Var i \<Longrightarrow> eval e \<equiv> i" by simp

lemma eval_add [hints]: "e \<equiv> Add e1 e2 \<Longrightarrow> m \<equiv> eval e1 \<Longrightarrow> n \<equiv> eval e2 \<Longrightarrow> eval e \<equiv> m + n"
by simp

ML_command\<open>
  val t1 = @{term_pat "eval ?e"}
  val t2 = @{term_pat "1 + (2 + 7) ::int"}
  val _ = Util.log_unif_results @{context} (t1, t2) unify
\<close>

subsubsection \<open>Arithmetic with Environment\<close>
datatype AdvExpr =
  Unit
| Var nat
| Mul AdvExpr AdvExpr
| Inv AdvExpr

fun eval_adv :: "AdvExpr \<times> real list \<Rightarrow> real" where
  "eval_adv (Unit, \<Gamma>) = 1"
| "eval_adv (Var i, \<Gamma>) = \<Gamma> ! i"
| "eval_adv (Mul e1 e2, \<Gamma>) = eval_adv (e1, \<Gamma>) * eval_adv (e2, \<Gamma>)"
| "eval_adv (Inv e, \<Gamma>) = inverse (eval_adv (e, \<Gamma>))"

(*hint to split expression and environment*)
lemma eval_adv_split [hints]: "e \<equiv> (e1, \<Gamma>) \<Longrightarrow> n \<equiv> eval_adv (e1, \<Gamma>) \<Longrightarrow> eval_adv e \<equiv> n"
by simp

(*hints for environment lookup*)
lemma eval_adv_Uar_Suc [hints]:
  "e \<equiv> Var (Suc p) \<Longrightarrow> \<Gamma> \<equiv> s # \<Delta> \<Longrightarrow> n \<equiv> eval_adv (Var p, \<Delta>) \<Longrightarrow> eval_adv (e, \<Gamma>) \<equiv> n"
by simp

lemma eval_adv_Var_zero [hints]: "e \<equiv> Var 0 \<Longrightarrow> \<Gamma> \<equiv> n # \<Theta> \<Longrightarrow> eval_adv (e, \<Gamma>) \<equiv> n" by simp

(*hints for expressions*)
lemma eval_adv_Unit [hints]: "e \<equiv> Unit \<Longrightarrow> eval_adv (e, \<Gamma>) \<equiv> 1" by simp

lemma eval_adv_Mul [hints]:
  "e \<equiv> Mul e1 e2 \<Longrightarrow> m \<equiv> eval_adv (e1, \<Gamma>) \<Longrightarrow> n \<equiv> eval_adv (e2, \<Gamma>) \<Longrightarrow> eval_adv (e, \<Gamma>) \<equiv> m * n"
by simp

lemma eval_adv_Inv [hints]: "e1 \<equiv> Inv e2 \<Longrightarrow> n \<equiv> eval_adv (e2, \<Gamma>) \<Longrightarrow> eval_adv (e1, \<Gamma>) \<equiv> inverse n"
by simp

ML_command\<open>
  val t1 = @{term_pat "eval_adv ?e"};
  val t2 = @{term_pat "1 * inverse 3 * 5 :: real"}
  val _ = Util.log_unif_results' 1 @{context} (t1, t2) unify
\<close>

end
