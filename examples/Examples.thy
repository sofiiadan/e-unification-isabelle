theory Examples
imports
  Unification_Hints
  Complex_Main
begin


ML\<open>
  val t =
    Var (("v", 0), TFree ("'a", []) --> TFree ("'b", [])) $
      Var (("w", 0), TFree ("'a", []))
  val s =
    Var (("x", 0), TFree ("'a", []) --> TFree ("'b", [])) $
      Var (("y", 0), TFree ("'a", []))
  (*returns empty environment and no unification error*)
  val env = 
    Unify.unifiers ((Context.the_generic_context ()), Envir.init, [(t,s)]) |> Seq.hd |> fst
  
  (*returns correct unifier*)
  val s' = (Var (("x", 0), TFree ("'b", [])))
  val env' = 
    Unify.unifiers ((Context.the_generic_context ()), Envir.init, [(t, s')]) |> Seq.hd |> fst
\<close>

ML\<open>
  Theory.setup (
    ML_Antiquotation.inline_embedded \<^binding>\<open>term_pat\<close>
    (Args.term_pattern >> (ML_Syntax.atomic o ML_Syntax.print_term)))
\<close>

ML\<open>
  open Unification_Util
  val hint_unif = Higher_Order_Pattern_Unification.unify_hints;
  val gen_ctxt = Context.the_generic_context
\<close>

declare [[log_level=500]]

(* Simple Recursive Hint Unification Examples *)
(* 1 *)
lemma suc_one [hints]:
  "x \<equiv> 1 \<Longrightarrow> Suc x \<equiv> 2"
by linarith

lemma add_zero [hints]:
  "y \<equiv> z \<Longrightarrow> x \<equiv> 0 \<Longrightarrow> (y::nat) \<equiv> z + x"
by simp

ML\<open>
  val (t1,t2) = (@{term_pat "Suc (?n + 0)"},@{term_pat "2::nat"})\<close>
  
ML\<open>
  val (env,thm) = hint_unif (gen_ctxt ()) (t1,t2) (Envir.empty 0);
  trace_unif_result @{context} (t1,t2) (env,thm)\<close>

(* 2 *)
consts f :: "nat \<Rightarrow> nat" g :: "nat \<Rightarrow> nat" h :: "nat \<Rightarrow> nat"
       a :: nat b :: nat
       
lemma [hints]:"X \<equiv> f \<Longrightarrow> X a \<equiv> X b"
  sorry

lemma [hints]:"X \<equiv> Y \<Longrightarrow> h (g X) \<equiv> g (h Y)"
  sorry

ML\<open>
  val (t1,t2) = (@{term_pat "h (g (f a))"},@{term_pat "g (h (f b))"})\<close>
  
ML\<open>
  val (env,thm) = hint_unif (gen_ctxt ()) (t1,t2) (Envir.empty 0);
  trace_unif_result @{context} (t1,t2) (env,thm)\<close>

(* Simple Reflexive Tactics *)

datatype Expr = Var int | Op Expr Expr

fun eval :: "Expr \<Rightarrow> int" where
  "eval (Var i) = i"
| "eval (Op ex1 ex2) = (eval ex1) + (eval ex2)"

consts simpl :: "Expr \<Rightarrow> Expr"

lemma soundness :
  "P (eval (simpl x)) \<Longrightarrow> P (eval x)"
sorry


(*supply base case and inductive hint*)
lemma h_base [hints]:
  "x \<equiv> Var i \<Longrightarrow> eval x \<equiv> i"
by simp

lemma h_add [hints]:
  "x \<equiv> Op z1 z2 \<Longrightarrow> m \<equiv> eval z1 \<Longrightarrow> n \<equiv> eval z2 \<Longrightarrow> eval x \<equiv> m + n"
by simp


ML\<open>
  val t1 = @{term_pat "eval ?y"};
  val t2 = @{term_pat "1 + (2 + 3) ::int"}\<close>

ML\<open>
  val (env,thm) = hint_unif (gen_ctxt ()) (t1,t2) (Envir.empty 0);
  trace_unif_result @{context} (t1,t2) (env,thm)\<close>


(* Advanced Reflexive Tactics *)
datatype AdvExpr =
    EUnit
  | EVar nat
  | EMult AdvExpr AdvExpr
  | EOpp AdvExpr

fun eval_adv :: "AdvExpr \<times> real list \<Rightarrow> real" where
    "eval_adv (EUnit,\<Gamma>) = 1"
  | "eval_adv (EVar i,\<Gamma>) = \<Gamma>!i"
  | "eval_adv (EMult ex1 ex2,\<Gamma>) = eval_adv (ex1,\<Gamma>) * eval_adv (ex2,\<Gamma>)"
  | "eval_adv (EOpp ex,\<Gamma>) = inverse (eval_adv (ex,\<Gamma>))"


(*hints for heap lookup*)
lemma h_var_base [hints]:
  "x \<equiv> EVar 0 \<Longrightarrow> \<Gamma> \<equiv> n#\<Theta> \<Longrightarrow> eval_adv (x,\<Gamma>) \<equiv> n"
by simp

lemma h_var_rec [hints]:
  "x \<equiv> EVar (Suc p) \<Longrightarrow> \<Gamma> \<equiv> s#\<Delta> \<Longrightarrow> n \<equiv> eval_adv (EVar p,\<Delta>) \<Longrightarrow> eval_adv (x,\<Gamma>) \<equiv> n"
by simp

(*hints for expressions*)
lemma h_unit [hints]:
  "x \<equiv> EUnit \<Longrightarrow> eval_adv (x,\<Gamma>) \<equiv> 1"
by simp
  
lemma h_times [hints]:
  "x \<equiv> EMult z1 z2 \<Longrightarrow> m \<equiv> eval_adv (z1,\<Gamma>) \<Longrightarrow> n \<equiv> eval_adv (z2,\<Gamma>) \<Longrightarrow> eval_adv (x,\<Gamma>) \<equiv> m * n"
by simp

lemma h_opp [hints]:
  "x \<equiv> EOpp z \<Longrightarrow> n \<equiv> eval_adv (z,\<Gamma>) \<Longrightarrow> eval_adv (x,\<Gamma>) \<equiv> inverse n"
by simp

ML\<open>
  val t1 = @{term_pat "eval_adv (?y,[3,5])"};
  val t2 = @{term_pat "1 * inverse 3 * 5::real"}\<close>

ML\<open>
  val (env,thm) = hint_unif (gen_ctxt ()) (t1,t2) (Envir.empty 0);
  trace_unif_result @{context} (t1,t2) (env,thm)\<close>

end