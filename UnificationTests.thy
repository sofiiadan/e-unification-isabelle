theory UnificationTests
imports
  Main
  First_Steps
begin

ML_file \<open>Test.ML\<close>
ML\<open>open Test\<close>

ML\<open>val hint_unif = Fou.first_order_unify_h
   val std_unif = Fou.first_order_unify\<close>

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

(* non-unifiable Var-free terms *)
ML\<open>test_group non_unif std_unif "Free only" free_gen\<close>
ML\<open>test_group non_unif hint_unif "Free only" free_gen\<close>
ML\<open>test_group non_unif_rev std_unif "Free only" free_gen\<close>
ML\<open>test_group non_unif_rev hint_unif "Free only" free_gen\<close>

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
ML\<open>list_pos @{context} std_unif "Var/Free, TVar/TFree combinations unify"
  [(Var(("A",0),TVar(("'a",0),[])),Free("A",TFree("'a",[]))),
   (Var(("A",0),TVar(("'a",0),[])),Var(("A",0),TFree("'a",[]))),
   (Var(("A",0),TVar(("'a",0),[])),Var(("B",0),TVar(("'a",0),[]))),
   (Var(("A",0),TVar(("'a",0),[])),Var(("A",0),TVar(("'b",0),[]))),
   (Var(("A",0),TFree("'a",[])),Free("A",TVar(("'a",0),[]))),
   (Free("A",TFree("'a",[])),Free("A",TVar(("'a",0),[])))]\<close>

(* should unify, using hint_unif *)
ML\<open>list_pos @{context} hint_unif "Var/Free, TVar/TFree combinations unify"
  [(Var(("A",0),TVar(("'a",0),[])),Free("A",TFree("'a",[]))),
   (Var(("A",0),TVar(("'a",0),[])),Var(("A",0),TFree("'a",[]))),
   (Var(("A",0),TVar(("'a",0),[])),Var(("B",0),TVar(("'a",0),[]))),
   (Var(("A",0),TVar(("'a",0),[])),Var(("A",0),TVar(("'b",0),[]))),
   (Var(("A",0),TFree("'a",[])),Free("A",TVar(("'a",0),[]))),
   (Free("A",TFree("'a",[])),Free("A",TVar(("'a",0),[])))]\<close>

(* should not unify, using std_unif *)
ML\<open>list_neg @{context} std_unif "Different Free/TFree fails"
  [(Free("A",TFree("'a",[])),Free("A",TFree("'b",[]))),
   (Free("A",TFree("'a",[])),Free("B",TFree("'a",[])))]\<close>
(* should not unify, using hint_unif *)
ML\<open>list_neg @{context} hint_unif "Different Free/TFree fails"
  [(Free("A",TFree("'a",[])),Free("A",TFree("'b",[]))),
   (Free("A",TFree("'a",[])),Free("B",TFree("'a",[])))]\<close>

(** hint tests **)

(* non-recursive hint tests *)

(*add_zero*)
ML\<open>single_neg @{context} hint_unif "add_zero without hint"
  (@{term_pat "5::nat"},
   @{term_pat "?b + 0 ::nat"})\<close>
lemma add_zero [hints]: "Y \<equiv> Z \<Longrightarrow> X \<equiv> (0::nat) \<Longrightarrow> Y + X \<equiv> Z"
  by simp
ML\<open>single_pos @{context} hint_unif "add_zero with hint"
  (@{term_pat "5::nat"},
   @{term_pat "?b + 0 ::nat"})\<close>

(*mult_one*)
ML\<open>single_neg @{context} hint_unif "mult_one without hint"
  (@{term_pat "1::nat"},
    @{term_pat "?a * ?b ::nat"})\<close>
lemma mult_one [hints]: "X \<equiv> 1 \<Longrightarrow> Y \<equiv> 1 \<Longrightarrow> X * Y \<equiv> (1::nat)"
  by simp
ML\<open>single_pos @{context} hint_unif "mult_one with hint"
  (@{term_pat "1::nat"},
   @{term_pat "?a * ?b ::nat"})\<close>

(*id_eq*)
ML\<open>single_neg @{context} hint_unif "id_eq without hint"
  (@{term_pat "5::nat"},
   @{term_pat "id ?a ::nat"})\<close>
lemma ID_EQ [hints]: "X \<equiv> Y \<Longrightarrow> id X \<equiv> Y"
  by simp
ML\<open>single_pos @{context} hint_unif "id_eq with hint"
  (@{term_pat "5::nat"},
   @{term_pat "id ?a ::nat"})\<close>

(*Suc 2 = 3*)
ML\<open>single_neg @{context} hint_unif "Suc ?x = 3 without hint"
  (@{term_pat "Suc ?x ::nat"},
   @{term_pat "3::nat"})\<close>
lemma suc2 [hints]: "X \<equiv> 2 \<Longrightarrow> Suc X \<equiv> 3"
  by linarith
ML\<open>single_pos @{context} hint_unif "Suc ?x = 3 with hint"
  (@{term_pat "Suc ?x ::nat"},
   @{term_pat "3::nat"})\<close>

(*Suc x = 4, multiple matching hints, first one doesn't unify*)
definition x_def: "x\<equiv>3::nat"
ML\<open>single_neg @{context} hint_unif "Suc x = 4 without hint"
  (@{term_pat "Suc x ::nat"},
   @{term_pat "4::nat"})\<close>
lemma suc_x_4 [hints]: "Suc x \<equiv> 4"
  by (simp add:x_def)
lemma suc3 [hints]: "X \<equiv> 3 \<Longrightarrow> Suc X \<equiv> 4"
  by linarith
ML\<open>single_pos @{context} hint_unif "Suc x = 4 with multiple matching hints, only second one solves"
  (@{term_pat "Suc x ::nat"},
   @{term_pat "4::nat"})\<close>

(* recursive hint tests *)

declare [[log_level=1000]]

(*Suc (Suc 0) = 2*)
ML\<open>single_neg @{context} hint_unif "Suc ?x = 3 without hint"
  (@{term_pat "Suc (Suc ?X) ::nat"},
   @{term_pat "2::nat"})\<close>
lemma suc0 [hints]: "X \<equiv> 0 \<Longrightarrow> Suc X \<equiv> 1"
  by linarith
lemma suc1 [hints]: "X \<equiv> 1 \<Longrightarrow> Suc X \<equiv> 2"
  by linarith
ML\<open>single_pos @{context} hint_unif "Suc ?x = 3 with hint"
  (@{term_pat "Suc (Suc ?X) ::nat"},
   @{term_pat "2::nat"})\<close>


ML\<open>
  single_pos @{context} hint_unif ""
    (@{term_pat "id 5 ::nat"},
     @{term_pat "Suc (Suc 5)"})\<close>

ML\<open>
  single_pos @{context} hint_unif ""
    (@{term_pat "r ((id 5) + (2 - Suc (id ?Y)) = Suc 4)::nat"},
     @{term_pat "(id r) (5 = id (Suc 4))::nat"})\<close>

end