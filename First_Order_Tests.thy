theory First_Order_Tests
imports
  Hint_Unification
begin

ML_file \<open>Test.ML\<close>

ML\<open>
  open Test
  open Utils
  val hint_unif = FO_Hint_Unif.fo_unify_hints
  val std_unif = FO_Hint_Unif.fo_unify
  val ctxt = Context.the_generic_context
\<close>

setup\<open>term_pat_setup\<close>

declare [[log_level=500]]

(* Symmetry *)
ML\<open>test_group symmetry std_unif "Free/Var" free_var_gen\<close>
ML\<open>test_group symmetry hint_unif "Free/Var" free_var_gen\<close>

(* Unification of identical terms does not change environment *)
ML\<open>test_group noop std_unif "Free/Var" free_var_gen\<close>
ML\<open>test_group noop hint_unif "Free/Var" free_var_gen\<close>

(* Correct theorem is returned *)
ML\<open>test_group theorem_correctness std_unif "Free/Var" free_var_gen\<close>
ML\<open>test_group theorem_correctness hint_unif "Free/Var" free_var_gen\<close>

ML\<open>test_group theorem_correctness_var_term std_unif "Free/Var" free_var_gen\<close>
ML\<open>test_group theorem_correctness_var_term hint_unif "Free/Var" free_var_gen\<close>

ML\<open>test_group theorem_correctness_vars_replaced std_unif "Free/Var" free_var_gen\<close>
ML\<open>test_group theorem_correctness_vars_replaced hint_unif "Free/Var" free_var_gen\<close>

(* Correct Environment is returned *)
ML\<open>test_group sigma_unifies std_unif "Free/Var" free_var_gen\<close>
ML\<open>test_group sigma_unifies hint_unif "Free/Var" free_var_gen\<close>

ML\<open>test_group sigma_unifies_var_term std_unif "Free/Var" free_var_gen\<close>
ML\<open>test_group sigma_unifies_var_term hint_unif "Free/Var" free_var_gen\<close>

ML\<open>test_group sigma_unifies_vars_replaced std_unif "Free/Var" free_var_gen\<close>
ML\<open>test_group sigma_unifies_vars_replaced hint_unif "Free/Var" free_var_gen\<close>


(** non-unifiability tests **)
(* Occurs check stops unification *)
ML\<open>test_group occurs_check std_unif "Var only" var_gen\<close>
ML\<open>test_group occurs_check hint_unif "Var only" var_gen\<close>


(** unifiability tests **)
(* Unification of identical terms *)
ML\<open>test_group identical_unif std_unif "Free/Var" free_var_gen\<close>
ML\<open>test_group identical_unif hint_unif "Free/Var" free_var_gen\<close>

(* Var x unifies with arbitrary term not containing x *)
ML\<open>test_group unif_var_term std_unif "Free/Var" free_var_gen\<close>
ML\<open>test_group unif_var_term hint_unif "Free/Var" free_var_gen\<close>

(* term unifies with term where all Vars are replaced by Frees *)
ML\<open>test_group unif_vars_replaced std_unif "Free/Var" free_var_gen\<close>
ML\<open>test_group unif_vars_replaced hint_unif "Free/Var" free_var_gen\<close>

(** manual tests with Var/Free and TVar/TFree **)
(* should unify, using std_unif *)
ML\<open>list_pos (ctxt ()) std_unif "Var/Free, TVar/TFree combinations unify"
  [(Var(("A",0),TVar(("'a",0),[])),Free("A",TFree("'a",[]))),
   (Var(("A",0),TVar(("'a",0),[])),Var(("A",0),TFree("'a",[]))),
   (Var(("A",0),TVar(("'a",0),[])),Var(("B",0),TVar(("'a",0),[]))),
   (Var(("A",0),TVar(("'a",0),[])),Var(("A",0),TVar(("'b",0),[]))),
   (Var(("A",0),TFree("'a",[])),Free("A",TVar(("'a",0),[]))),
   (Free("A",TFree("'a",[])),Free("A",TVar(("'a",0),[])))]\<close>

(* should unify, using hint_unif *)
ML\<open>list_pos (ctxt ()) hint_unif "Var/Free, TVar/TFree combinations unify"
  [(Var(("A",0),TVar(("'a",0),[])),Free("A",TFree("'a",[]))),
   (Var(("A",0),TVar(("'a",0),[])),Var(("A",0),TFree("'a",[]))),
   (Var(("A",0),TVar(("'a",0),[])),Var(("B",0),TVar(("'a",0),[]))),
   (Var(("A",0),TVar(("'a",0),[])),Var(("A",0),TVar(("'b",0),[]))),
   (Var(("A",0),TFree("'a",[])),Free("A",TVar(("'a",0),[]))),
   (Free("A",TFree("'a",[])),Free("A",TVar(("'a",0),[])))]\<close>

(* should not unify, using std_unif *)
ML\<open>list_neg (ctxt ()) std_unif "Different Free/TFree fails"
  [(Free("A",TFree("'a",[])),Free("A",TFree("'b",[]))),
   (Free("A",TFree("'a",[])),Free("B",TFree("'a",[])))]\<close>
(* should not unify, using hint_unif *)
ML\<open>list_neg (ctxt ()) hint_unif "Different Free/TFree fails"
  [(Free("A",TFree("'a",[])),Free("A",TFree("'b",[]))),
   (Free("A",TFree("'a",[])),Free("B",TFree("'a",[])))]\<close>

(** hint tests **)
(*use <trace_test_result (ctxt()) (t1,t2) hint_unif> to view unification result*)

(* non-recursive hint tests *)

(*add_zero*)
ML\<open>
  val (t1,t2) = (@{term_pat "5::nat"}, @{term_pat "?b + 0 ::nat"});
  single_neg (ctxt ()) hint_unif "add_zero without hint" (t1,t2)\<close>
lemma add_zero [hints]: "Y \<equiv> Z \<Longrightarrow> X \<equiv> (0::nat) \<Longrightarrow> Y + X \<equiv> Z"
  by simp
ML\<open>single_pos (ctxt ()) hint_unif "add_zero with hint" (t1,t2)\<close>

(*mult_one*)
ML\<open>
  val (t1,t2) = (@{term_pat "1::nat"},@{term_pat "?a * ?b ::nat"});
  single_neg (ctxt ()) hint_unif "mult_one without hint" (t1,t2)\<close>
lemma mult_one [hints]: "X \<equiv> 1 \<Longrightarrow> Y \<equiv> 1 \<Longrightarrow> X * Y \<equiv> (1::nat)"
  by simp
ML\<open>single_pos (ctxt ()) hint_unif "mult_one with hint" (t1,t2)\<close>

(*id_eq*)
ML\<open>
  val (t1,t2) = (@{term_pat "5::nat"},@{term_pat "id ?a ::nat"});
  single_neg (ctxt ()) hint_unif "id_eq without hint" (t1,t2)\<close>
lemma ID_EQ [hints]: "X \<equiv> Y \<Longrightarrow> id X \<equiv> Y"
  by simp
ML\<open>single_pos (ctxt ()) hint_unif "id_eq with hint" (t1,t2)\<close>

(*Suc 2 = 3*)
ML\<open>
  val (t1,t2) = (@{term_pat "Suc ?x ::nat"},@{term_pat "3::nat"});
  single_neg (ctxt ()) hint_unif "Suc ?x = 3 without hint" (t1,t2)\<close>
lemma suc2 [hints]: "X \<equiv> 2 \<Longrightarrow> Suc X \<equiv> 3"
  by linarith
ML\<open>single_pos (ctxt ()) hint_unif "Suc ?x = 3 with hint" (t1,t2)\<close>

(*Suc x = 4, multiple matching hints, first one doesn't unify*)
definition x_def: "x\<equiv>3::nat"
ML\<open>
  val (t1,t2) =(@{term_pat "Suc x ::nat"},@{term_pat "4::nat"});
  single_neg (ctxt ()) hint_unif "Suc x = 4 without hint" (t1,t2)\<close>
lemma suc_x_4 [hints]: "Suc x \<equiv> 4"
  by (simp add:x_def)
lemma suc3 [hints]: "X \<equiv> 3 \<Longrightarrow> Suc X \<equiv> 4"
  by linarith
ML\<open>single_pos (ctxt ()) hint_unif "Suc x = 4 with multiple matching hints, only second one solves"
  (t1,t2)\<close>

(* recursive hint tests *)

(*Suc (Suc 0) = 2*)
ML\<open>
  val (t1,t2) = (@{term_pat "Suc (Suc ?X) ::nat"},@{term_pat "2::nat"});
  single_neg (ctxt ()) hint_unif "Suc ?x = 3 without hint" (t1,t2)\<close>
lemma suc0 [hints]: "X \<equiv> 0 \<Longrightarrow> Suc X \<equiv> 1"
  by linarith
lemma suc1 [hints]: "X \<equiv> 1 \<Longrightarrow> Suc X \<equiv> 2"
  by linarith
ML\<open>single_pos (ctxt ()) hint_unif "Suc ?x = 3 with hints" (t1,t2)\<close>


consts f :: "nat \<Rightarrow> nat" g :: "nat \<Rightarrow> nat" h :: "nat \<Rightarrow> nat"
       a :: nat b :: nat y::nat

lemma [hints] : "X \<equiv> f (g 0) \<Longrightarrow> Y \<equiv> g (f 0) \<Longrightarrow> f (g X) \<equiv> g (f Y)"
  sorry
ML\<open>
  val (t1,t2) = (@{term_pat "f (g (f (g 0))) ::nat"}, @{term_pat "g (f (g (f 0))) ::nat"});
  single_pos (ctxt ()) hint_unif "" (t1,t2);\<close>

(*same hint but with premises switched*)
consts f2 :: "nat \<Rightarrow> nat" g2 :: "nat \<Rightarrow> nat"
lemma [hints] : "Y \<equiv> g2 (f2 0) \<Longrightarrow> X \<equiv> f2 (g2 0) \<Longrightarrow> f2 (g2 X) \<equiv> g2 (f2 Y)"
  sorry
ML\<open>
  val (t1,t2) = (@{term_pat "f2 (g2 (f2 (g2 0))) ::nat"}, @{term_pat "g2 (f2 (g2 (f2 0))) ::nat"});
  single_pos (ctxt ()) hint_unif "" (t1,t2);\<close>

lemma [hints]: "Y \<equiv> f X \<Longrightarrow> X \<equiv> f (g 0) \<Longrightarrow>  f (g X) \<equiv> g (f Y)"
  sorry
ML\<open>
  val (t1,t2) = (@{term_pat "f (g (f (g 0))) ::nat"}, @{term_pat "g (f (f (f (g 0)))) ::nat"});
  single_pos (ctxt ()) hint_unif "" (t1,t2);\<close>

(*same hint but with premises switched*)
lemma [hints]: "X \<equiv> f2 (g2 0) \<Longrightarrow> Y \<equiv> f2 X \<Longrightarrow>  f2 (g2 X) \<equiv> g2 (f2 Y)"
  sorry
ML\<open>
  val (t1,t2) = (@{term_pat "f2 (g2 (f2 (g2 0))) ::nat"}, @{term_pat "g2 (f2 (f2 (f2 (g2 0)))) ::nat"});
  single_pos (ctxt ()) hint_unif "" (t1,t2);\<close>

(*recursive calls with encapsulated hints*)
lemma [hints]:"X \<equiv> f \<Longrightarrow> X a \<equiv> X b"
  sorry

lemma [hints]:"X \<equiv> Y \<Longrightarrow> h (g X) \<equiv> g (h Y)"
  sorry

ML\<open>
  val (t1,t2) = (@{term_pat "h (g (f a))"},@{term_pat "g (h (f b))"});
  single_pos (ctxt ()) hint_unif "" (t1,t2);
\<close>

ML\<open>
  val (t1,t2) = (@{term_pat "id (id 2) ::nat"}, @{term_pat "Suc ?x ::nat"});
  single_pos (ctxt ()) hint_unif "" (t1,t2);
\<close>

(*recursive calls with alternating hints*)
lemma [hints]:"X \<equiv> Y \<Longrightarrow> f X \<equiv> g Y"
  sorry

lemma [hints]:"X \<equiv> Y \<Longrightarrow> f2 X \<equiv> g2 Y"
  sorry

ML\<open>
  val (t1,t2) = (@{term_pat "f2 (f (g 0)) ::nat"}, @{term_pat "g2 (f (g 0)) ::nat"});
  single_pos (ctxt ()) hint_unif "" (t1,t2)\<close>


(*premise order: case where Xi depends on Xj with j>i cannot unify*)
consts n::nat m::nat 

lemma h1[hints]: "X1 \<equiv> X2 n \<Longrightarrow> X2 \<equiv> f \<Longrightarrow> X1 \<equiv> f m"
  sorry

ML\<open>
  val (t1,t2) = (@{term_pat "f n ::nat"}, @{term_pat "f m ::nat"});
  single_neg (ctxt ()) hint_unif "" (t1,t2);\<close>


end