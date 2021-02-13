theory UnificationTests
imports Main "spec_check/src/Spec_Check" First_Steps
begin

ML_file "Test.ML"
ML\<open>open Test\<close>

ML\<open>
val hint_unif = Fou.first_order_unify_h
val std_unif = Fou.first_order_unify_thm
fun test_with test unif gen_name gen n =
  test @{context} unif (gen_name^", size "^Int.toString n) (gen n)
fun gen_test_group test unif gen_name gen =
  map (test_with test unif gen_name gen)
fun test_group test unif gen_name gen =
  fold (fn test => fn _ => test (Random.new ())) (gen_test_group test unif gen_name gen [1,2,5,10,50]) ()

\<close>
(* Symmetry *)
ML\<open>test_group test_symmetry std_unif "Free/Var" free_var_gen\<close>
ML\<open>test_group test_symmetry hint_unif "Free/Var" free_var_gen\<close>

(* non-unifiable Var-free terms *)
ML\<open>test_group test_non_unif std_unif "Free only" free_gen\<close>
ML\<open>test_group test_non_unif hint_unif "Free only" free_gen\<close>
ML\<open>test_group test_non_unif std_unif "Free only" free_gen\<close>
ML\<open>test_group test_non_unif hint_unif "Free only" free_gen\<close>

(* Occurs check, tests fail for terms of size 1 (identical Vars) *)
ML\<open>test_group test_occurs_check std_unif "Var only" var_gen\<close>
ML\<open>test_group test_occurs_check hint_unif "Var only" var_gen\<close>

(* Var, term unification *)
(* type issue; function argument type /= function type *)
ML\<open>test_group test_unif_var_term std_unif "Free/Var" free_var_gen\<close>
ML\<open>test_group test_unif_var_term hint_unif "Free/Var" free_var_gen\<close>

(* Unification of identical terms *)
ML\<open>test_group test_identical_unif std_unif "Free/Var" free_var_gen\<close>
ML\<open>test_group test_identical_unif hint_unif "Free/Var" free_var_gen\<close>

(* Unification of identical terms does not change environment *)
ML\<open>test_group test_noop std_unif "Free/Var" free_var_gen\<close>
ML\<open>test_group test_noop hint_unif "Free/Var" free_var_gen\<close>

(* Correct theorem is returned *)
ML\<open>test_group test_theorem_correctness std_unif "Free/Var" free_var_gen\<close>
ML\<open>test_group test_theorem_correctness hint_unif "Free/Var" free_var_gen\<close>

ML\<open>test_group test_theorem_correctness_var_term std_unif "Free/Var" free_var_gen\<close>
ML\<open>test_group test_theorem_correctness_var_term hint_unif "Free/Var" free_var_gen\<close>

ML\<open>test_hunif (@{term_pat "?v1_7.0 ?v0_6.0"}, @{term_pat "?v1_1.0 f0_8"})\<close>

(* Correct Environment is returned *)
ML\<open>test_group test_sigma_unifies std_unif "Free/Var" free_var_gen\<close>
ML\<open>test_group test_sigma_unifies hint_unif "Free/Var" free_var_gen\<close>

(* multiple identical Vars can lead to failing tests *)
ML\<open>test_group test_unif_vars_replaced std_unif "Free/Var" free_var_gen\<close>
ML\<open>test_group test_unif_vars_replaced hint_unif "Free/Var" free_var_gen\<close>


(* Manual tests with Var/Free and TVar/TFree *)
(* should unify, using std_unif *)
ML\<open>test_list_pos @{context} std_unif "Var/Free, TVar/TFree combinations unify"
  [(Var(("A",0),TVar(("'a",0),[])),Free("A",TFree("'a",[]))),
   (Var(("A",0),TVar(("'a",0),[])),Var(("A",0),TFree("'a",[]))),
   (Var(("A",0),TVar(("'a",0),[])),Var(("B",0),TVar(("'a",0),[]))),
   (Var(("A",0),TVar(("'a",0),[])),Var(("A",0),TVar(("'b",0),[]))),
   (Var(("A",0),TFree("'a",[])),Free("A",TVar(("'a",0),[]))),
   (Free("A",TFree("'a",[])),Free("A",TVar(("'a",0),[])))]\<close>

(* should unify, using hint_unif *)
ML\<open>test_list_pos @{context} hint_unif "Var/Free, TVar/TFree combinations unify"
  [(Var(("A",0),TVar(("'a",0),[])),Free("A",TFree("'a",[]))),
   (Var(("A",0),TVar(("'a",0),[])),Var(("A",0),TFree("'a",[]))),
   (Var(("A",0),TVar(("'a",0),[])),Var(("B",0),TVar(("'a",0),[]))),
   (Var(("A",0),TVar(("'a",0),[])),Var(("A",0),TVar(("'b",0),[]))),
   (Var(("A",0),TFree("'a",[])),Free("A",TVar(("'a",0),[]))),
   (Free("A",TFree("'a",[])),Free("A",TVar(("'a",0),[])))]\<close>

(* should not unify, using std_unif *)
ML\<open>test_list_neg @{context} std_unif "Different Free/TFree fails"
  [(Free("A",TFree("'a",[])),Free("A",TFree("'b",[]))),
   (Free("A",TFree("'a",[])),Free("B",TFree("'a",[])))]\<close>
(* should not unify, using hint_unif *)
ML\<open>test_list_neg @{context} hint_unif "Different Free/TFree fails"
  [(Free("A",TFree("'a",[])),Free("A",TFree("'b",[]))),
   (Free("A",TFree("'a",[])),Free("B",TFree("'a",[])))]\<close>

(* Hint tests *)

(* add_zero *)
ML\<open>test_list_neg @{context} hint_unif "add_zero without hint" [(@{term_pat "5::nat"},@{term_pat "?b + 0 ::nat"})]\<close>
lemma add_zero [hints]:
  "Y \<equiv> Z \<Longrightarrow> X \<equiv> (0::nat) \<Longrightarrow> Y + X \<equiv> Z"
  by simp
ML\<open>test_list_pos @{context} hint_unif "add_zero with hint" [(@{term_pat "5::nat"},@{term_pat "?b + 0 ::nat"})]\<close>

(* mult_one *)
ML\<open>test_not_unif @{context} hint_unif (@{term_pat "1::nat"},@{term_pat "?a * ?b ::nat"})\<close>
lemma mult_one [hints]:
  "X \<equiv> 1 \<Longrightarrow> Y \<equiv> 1 \<Longrightarrow> X * Y \<equiv> (1::nat)"
  by simp
ML\<open>test_unif @{context} hint_unif (@{term_pat "1::nat"},@{term_pat "?a * ?b ::nat"})\<close>

(* id_eq *)
ML\<open>test_not_unif @{context} hint_unif (@{term_pat "5::nat"},@{term_pat "id ?a ::nat"})\<close>
lemma ID_EQ [hints]:
  "X \<equiv> Y \<Longrightarrow> id X \<equiv> Y"
  by simp
ML\<open>test_unif @{context} hint_unif (@{term_pat "5::nat"},@{term_pat "id ?a ::nat"})\<close>

(* Suc 2 = 3 *)
ML\<open>test_not_unif @{context} hint_unif (@{term_pat "Suc ?x ::nat"},@{term_pat "3::nat"})\<close>
lemma suc2 [hints]:
  "X \<equiv> 2 \<Longrightarrow> Suc X \<equiv> 3"
  by linarith
ML\<open>test_unif @{context} hint_unif (@{term_pat "Suc ?x ::nat"},@{term_pat "3::nat"})\<close>

end