signature TEST = 
sig
  type unificationf
  type unif_test
  type unif_test_gen
  val unification : Proof.context -> unificationf -> Envir.env -> (term * term) -> (Envir.env * thm)

  val free_gen : int -> term Gen_Term.gen
  val var_gen : int -> term Gen_Term.gen
  val free_var_gen : int -> term Gen_Term.gen
  val free_var_gen_50000_ids : int -> term Gen_Term.gen

  val terms_unify : Proof.context -> unificationf -> Envir.env  -> (term * term) -> bool
  val test_unif : Proof.context -> unificationf -> (term * term) -> unit
  val test_not_unif : Proof.context -> unificationf -> (term * term) -> unit
  val test_list_pos : Proof.context -> (Proof.context -> term * term -> Envir.env -> 'a * 'b) -> string -> (term * term) list -> unit
  val test_list_neg : Proof.context -> (Proof.context -> term * term -> Envir.env -> 'a * 'b) -> string -> (term * term) list -> unit
  val test_symmetry : unif_test_gen
  val test_sigma_unifies : unif_test_gen
  val test_theorem_correctness : unif_test_gen
  val test_theorem_correctness_var_term : unif_test_gen
  val test_non_unif : unif_test_gen
  val test_non_unif_rev : unif_test_gen
  val test_identical_unif : unif_test_gen
  val test_unif_var_term : unif_test_gen
  val test_unif_vars_replaced : unif_test_gen
  val test_noop : unif_test_gen
  val test_occurs_check : unif_test_gen
end

structure Test : TEST =
struct
type unificationf = Proof.context -> term * term -> Envir.env -> (Envir.env * thm)
type unif_test = Proof.context -> unificationf -> Random.rand -> unit
type unif_test_gen = Proof.context -> unificationf -> string -> term Gen_Term.gen -> Random.rand -> unit

val free_gen = Gen_Term.term_fol (Gen_Term.def_sym_gen (1.0,0.0,0.0) 10) 5
val var_gen = Gen_Term.term_fol (Gen_Term.def_sym_gen (0.0,1.0,0.0) 10) 5
val free_var_gen = Gen_Term.term_fol (Gen_Term.def_sym_gen (0.5,0.5,0.0) 10) 5
val free_var_gen_50000_ids = Gen_Term.term_fol (Gen_Term.def_sym_gen (0.5,0.5,0.0) 50000) 5

val empty_env = Envir.empty 0

fun replace_vars x = case x of 
   Var ((x,_),tya) => Free (x,tya)
  |f$x => (replace_vars f) $ (replace_vars x)
  |t => t

(* generates a tuple of terms using generator tgen *)
fun gen_termtup tgen rand =
  let val (t1,rand1) = tgen rand
      val (t2,rand2) = tgen rand1
  in ((t1,t2),rand2) end

fun gen_var_termtup tgen rand =
  let val (t,rand) = tgen rand
  in ((Var(("AVAR",1001),TVar(("'atype",1001),[])),t),rand) end

fun gen_termtup_repl_vars tgen rand =
  let val (t,rand) = tgen rand
  in ((t,replace_vars t),rand) end

fun gen_identical_termtup tgen rand =
  let val (t,rand) = tgen rand
  in ((t,t),rand) end

fun gen_occurs_clash_termtup tgen rand =
  let val (t,rand) = tgen rand
      val var = hd (Term.add_vars t [])
  in ((Var var,t),rand) end

fun print_termtup ctxt (t1,t2) =
  (pretty_terms ctxt [t1,t2] |> Pretty.string_of)


(* checks if two terms unify using unif *)
fun terms_unify ctxt unif envir (t1,t2) =
  let val (env,thm) = unif ctxt (t1,t2) envir
  in true end handle _ => false

(* checks if the environment resulting from unif (t1,t2) unifies t1 and t2 *)
fun sigma_unifies ctxt unif envir (t1,t2) =
let val (sigma,_) = unif ctxt (t1,t2) envir in
   Envir.norm_term sigma t1 = Envir.norm_term sigma t2
end

fun sigma_unchanged ctxt unif ts =
let val (sigma,_) = unif ctxt ts empty_env in
  Envir.is_empty sigma
end

val terms_from_thm =
  (fn (Const ("Pure.eq",_) $ t1 $ t2) => (t1,t2)) o Thm.concl_of

(* checks if the theorem resulting from unif (t1,t2) unifies t1 and t2 *)
fun theorem_correct ctxt unif (t1,t2) =
let val (sigma,thm) = unif ctxt (t1,t2) empty_env
    val (lhs,rhs) = terms_from_thm thm in
  (Envir.norm_term sigma t1,Envir.norm_term sigma t2) = (lhs,rhs)
  orelse (Envir.norm_term sigma t1,Envir.norm_term sigma t2) = (rhs,lhs)
end

val term_is_var = fn Var _ => true | _ => false

fun unification ctxt unif envir (t1,t2) =
 let
    val _ = writeln "Terms: "
    val _ = pwriteln (pretty_term ctxt t1)
    val _ = pwriteln (pretty_term ctxt t2)
    val (env,thm) = unif ctxt (t1,t2) envir
    val _ = pretty_envs ctxt env
    val _ = pretty_thm ctxt thm
  in (env,thm) end

fun test_unif ctxt unif ts =
  if terms_unify ctxt unif empty_env ts then tracing "Unification succeeded" else warning "Unification failed"
fun test_not_unif ctxt unif ts=
  if not (terms_unify ctxt unif empty_env ts) then tracing "Unification failed" else warning "Unification succeeded"

fun test_list_pos ctxt unif name l = 
Spec_Check.check_seq ctxt name
  (Seq.of_list l)
  (SOME (print_termtup ctxt))
  (fn x=>[x])
  (Property.pred (terms_unify ctxt unif empty_env))

fun test_list_neg ctxt unif name l = 
Spec_Check.check_seq ctxt name
  (Seq.of_list l)
  (SOME (print_termtup ctxt))
  (fn x=>[x])
  (Property.pred (not o terms_unify ctxt unif empty_env))


(**)
fun test_termtup ctxt name prop gen =
  Spec_Check.check_gen ctxt name (gen_termtup gen) (SOME (print_termtup ctxt)) prop

fun test_symmetry ctxt unif gen_name gen =
let val terms_unify' = terms_unify ctxt unif empty_env in
  test_termtup ctxt
    ("Symmetry test: "^gen_name)
    (Property.==> (terms_unify',fn (t1,t2)=> terms_unify' (t2,t1)))
    gen
end

fun test_sigma_unifies ctxt unif gen_name =
test_termtup ctxt
  ("Sigma unifies terms: "^gen_name)
  (Property.==> (terms_unify ctxt unif empty_env,sigma_unifies ctxt unif empty_env))

fun test_sigma_unifies_repl_vars ctxt unif gen_name gen =
Spec_Check.check_gen ctxt
  ("Sigma unifies terms with replaced Vars: "^gen_name)
  (gen_termtup_repl_vars gen)
  (SOME (print_termtup ctxt))
  (Property.==> (terms_unify ctxt unif empty_env,theorem_correct ctxt unif))

fun test_theorem_correctness ctxt unif gen_name =
test_termtup ctxt
  ("Unifiability theorem correctness: "^gen_name)
  (Property.==> (terms_unify ctxt unif empty_env,theorem_correct ctxt unif))

fun test_theorem_correctness_var_term ctxt unif gen_name gen =
Spec_Check.check_gen ctxt
  ("Unifiability of Var with arbitrary term (not containing Var): "^gen_name)
  (gen_var_termtup gen)
  (SOME (print_termtup ctxt))
  (Property.==> (terms_unify ctxt unif empty_env,theorem_correct ctxt unif))

fun test_non_unif ctxt unif gen_name =
test_termtup ctxt
  ("Non-unifiability (inequality \<Longrightarrow> non-unifiability): "^gen_name)
  (Property.==> (<>,not o (terms_unify ctxt unif empty_env)))

fun test_non_unif_rev ctxt unif gen_name =
test_termtup ctxt
  ("Non-unifiability (non-unifiability \<Longrightarrow> inequality): "^gen_name)
  (Property.==> (not o (terms_unify ctxt unif empty_env),<>))

fun test_identical_unif ctxt unif gen_name gen =
Spec_Check.check_gen ctxt
  ("Unifiability of identical terms:"^gen_name)
  (gen_identical_termtup gen)
  (SOME (print_termtup ctxt))
  (Property.pred (terms_unify ctxt unif empty_env))

fun test_unif_var_term ctxt unif gen_name gen =
Spec_Check.check_gen ctxt
  ("Unifiability of Var with arbitrary term (not containing Var): "^gen_name)
  (gen_var_termtup gen)
  (SOME (print_termtup ctxt))
  (Property.pred (terms_unify ctxt unif empty_env))
  
fun test_unif_vars_replaced ctxt unif gen_name gen =
Spec_Check.check_gen ctxt
  ("Unifiability of t with t[Free/Var] (where all Vars are replaced by Frees): "^gen_name)
  (gen_termtup_repl_vars gen)
  (SOME (print_termtup ctxt))
  (Property.pred (terms_unify ctxt unif empty_env))

fun test_noop ctxt unif gen_name gen =
Spec_Check.check_gen ctxt
  ("Envir unchanged when unifying identical terms: "^gen_name)
  (gen_identical_termtup gen)
  (SOME (print_termtup ctxt))
  (Property.pred (sigma_unchanged ctxt unif))

fun test_occurs_check ctxt unif gen_name gen =
Spec_Check.check_gen ctxt
  ("Occurs check stops unification: "^gen_name)
  (gen_occurs_clash_termtup gen)
  (SOME (print_termtup ctxt))
  (Property.==> (not o term_is_var o snd,not o terms_unify ctxt unif empty_env))


end