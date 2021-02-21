signature TEST = 
sig
  
  type unificationf
  type unif_test_gen
  val unification : Proof.context -> unificationf -> Envir.env -> (term * term) -> (Envir.env * thm)

  val free_gen : int -> term Gen_Types.gen
  val var_gen : int -> term Gen_Types.gen
  val free_var_gen : int -> term Gen_Types.gen

  val test_group : unif_test_gen -> unificationf -> string -> (int -> term Gen_Types.gen) -> unit
  val test_list_pos : Proof.context -> unificationf -> string -> (term * term) list -> unit
  val test_list_neg : Proof.context -> unificationf -> string -> (term * term) list -> unit

  val test_symmetry : unif_test_gen
  val test_sigma_unifies : unif_test_gen
  val test_sigma_unifies_var_term : unif_test_gen
  val test_sigma_unifies_vars_replaced : unif_test_gen
  val test_theorem_correctness : unif_test_gen
  val test_theorem_correctness_var_term : unif_test_gen
  val test_theorem_correctness_vars_replaced : unif_test_gen
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
val ==> = Property.==>
infix ==>

type unificationf = Proof.context -> term * term -> Envir.env -> (Envir.env * thm)
type unif_test_gen = Proof.context -> unificationf -> string -> term Gen_Types.gen -> Random.rand -> unit

val free_gen = Gen_Term.term_fol (Gen_Term.def_sym_gen (1,0,0) 10) 5
val var_gen = Gen_Term.term_fol (Gen_Term.def_sym_gen (0,1,0) 10) 5
val free_var_gen = Gen_Term.term_fol (Gen_Term.def_sym_gen (1,1,0) 10) 5

val empty_env = Envir.empty 0

fun test_with test unif gen_name gen n =
  test @{context} unif (gen_name^", size "^Int.toString n) (gen n)

fun test_group test unif gen_name gen =
  fold
    (fn test => fn _ => test (Random.new ()))
    (map (test_with test unif gen_name gen) [1,2,5,10,50])
    ()

fun replace_vars x =
  case x of 
    Var ((x,_),tya) => Free (x,tya)
    |f$x => (replace_vars f) $ (replace_vars x)
    |t => t

fun incr_idx n =
   fn Var ((name,idx),typ) => Var ((name,idx+n),typ)
   |  Abs (s,T,t) => (Abs(s,T,incr_idx n t))
   |  t1 $ t2 => incr_idx n t1 $ incr_idx n t2
   |  t => t

(*TODO mehrere Vars/Frees mit gleichem Namen und unterschiedlichem Typ*)
fun gen_term_typed tgen rand =
  let val (t,r) = (tgen rand)
  in (Syntax.check_term (Proof_Context.set_mode Proof_Context.mode_schematic @{context}) t,r)
  end

(* generates a tuple of terms using generator tgen *)
fun gen_termtup tgen rand =
  let val (t1,rand1) = gen_term_typed tgen rand
      val (t2,rand2) = gen_term_typed tgen rand1
  in ((t1,incr_idx (Term.maxidx_of_term t1 +1) t2),rand2)
  end

fun gen_var_termtup tgen rand =
  let val (t,rand) = gen_term_typed tgen rand
  in ((Var(("AVAR",1001),TVar(("'atype",1001),[])),t),rand)
  end

fun gen_termtup_repl_vars tgen rand =
  let val (t,rand) = gen_term_typed tgen rand
  in ((t,replace_vars t),rand)
  end

fun gen_identical_termtup tgen rand =
  let val (t,rand) = gen_term_typed tgen rand
  in ((t,t),rand)
  end

fun gen_occurs_clash_termtup tgen rand =
  let val (t,rand) = gen_term_typed tgen rand
      val var = hd (Term.add_vars t [])
  in ((Var var,t),rand)
  end

fun print_termtup ctxt (t1,t2) =
  (Pretty.string_of (pretty_terms ctxt [t1,t2]))

fun print_termtup_unif ctxt unif (t1,t2) = 
  let val (env,thm) = unif ctxt (t1,t2) empty_env
  in (Pretty.string_of (pretty_terms ctxt [t1,t2])
      ^ "\nType Environment: "^ (Pretty.string_of (pretty_tyenv_p ctxt (Envir.type_env env)))
      ^ "\nTerm Environment: "^ (Pretty.string_of (pretty_env_p ctxt (Envir.term_env env)))
      ^ "\nTheorem: "^ (Pretty.string_of (pretty_thm ctxt thm))
      ^ "\nUnified terms: "^ (Pretty.string_of (pretty_terms ctxt [Envir.norm_term env t1,Envir.norm_term env t2])))
  end handle _ => "Unification failed, terms: "^print_termtup ctxt (t1,t2)

fun terms_match_size_eq ctxt (t1,t2) =
  let val _ = Pattern.match (Proof_Context.theory_of ctxt) (t1,t2) (Vartab.empty,Vartab.empty)
  in size_of_term t1 = size_of_term t2
  end handle _ => false

(* checks if two terms unify using unif *)
fun terms_unify ctxt unif envir (t1,t2) =
  let val (_,_) = unif ctxt (t1,t2) envir
  in true
  end handle _ => false

(* checks if the environment resulting from unif (t1,t2) unifies t1 and t2 *)
fun sigma_unifies ctxt unif (t1,t2) =
  let val (sigma,_) = unif ctxt (t1,t2) empty_env
  in Envir.norm_term sigma t1 = Envir.norm_term sigma t2
  end

fun sigma_unchanged ctxt unif ts =
  let val (sigma,_) = unif ctxt ts empty_env
  in Envir.is_empty sigma
  end

val terms_from_thm =
  (fn (Const ("Pure.eq",_) $ t1 $ t2) => (t1,t2)) o Thm.concl_of

(* checks if the theorem resulting from unif (t1,t2) unifies t1 and t2 *)
fun theorem_correct ctxt unif (t1,t2) =
  let val (sigma,thm) = unif ctxt (t1,t2) empty_env
      val (t1',t2') = (Envir.norm_term sigma t1,Envir.norm_term sigma t2)
      val (lhs,rhs) = terms_from_thm thm
  in (terms_match_size_eq ctxt (lhs,t1') andalso terms_match_size_eq ctxt (rhs,t2'))
    orelse (terms_match_size_eq ctxt (lhs,t2') andalso terms_match_size_eq ctxt (rhs,t1'))
  end handle _ => false

val term_is_var = fn Var _ => true | _ => false

fun unification ctxt unif envir (t1,t2) =
 let
    val _ = writeln "Terms: "
    val _ = pwriteln (pretty_term ctxt t1)
    val _ = pwriteln (pretty_term ctxt t2)
    val (env,thm) = unif ctxt (t1,t2) envir
    val _ = pretty_envs ctxt env
    val _ = pretty_thm ctxt thm
  in (env,thm)
  end

fun test_list_pos ctxt unif name l = 
  Spec_Check.check_seq ctxt name
    (Seq.of_list l)
    (SOME (print_termtup ctxt))
    (fn _=>[])
    (Property.property (terms_unify ctxt unif empty_env))

fun test_list_neg ctxt unif name l = 
  Spec_Check.check_seq ctxt name
    (Seq.of_list l)
    (SOME (print_termtup ctxt))
    (fn _=>[])
    (Property.property (not o terms_unify ctxt unif empty_env))

fun test_termtup ctxt name prop gen =
  Spec_Check.check_gen ctxt name
    (gen_termtup gen) 
    (SOME (print_termtup ctxt))
    prop

fun test_symmetry ctxt unif gen_name gen =
  let val terms_unify' = terms_unify ctxt unif empty_env
  in test_termtup ctxt
       ("Symmetry test: "^gen_name)
       (terms_unify' ==> (fn (t1,t2)=> terms_unify' (t2,t1)))
       gen
  end

fun test_noop ctxt unif gen_name gen =
  Spec_Check.check_gen ctxt
    ("Envir unchanged when unifying identical terms: "^gen_name)
    (gen_identical_termtup gen)
    (SOME (print_termtup ctxt))
    (Property.property (sigma_unchanged ctxt unif))

fun test_sigma_unifies ctxt unif gen_name =
  test_termtup ctxt
    ("Sigma unifies terms: "^gen_name)
    (terms_unify ctxt unif empty_env ==> sigma_unifies ctxt unif)

fun test_sigma_unifies_var_term ctxt unif gen_name gen =
  Spec_Check.check_gen ctxt
    ("Sigma unifies Var x with arbitrary term not containing x: "^gen_name)
    (gen_var_termtup gen)
    (SOME (print_termtup_unif ctxt unif))
    (terms_unify ctxt unif empty_env ==> theorem_correct ctxt unif)

fun test_sigma_unifies_vars_replaced ctxt unif gen_name gen =
  Spec_Check.check_gen ctxt
    ("Sigma unifies terms with replaced Vars: "^gen_name)
    (gen_termtup_repl_vars gen)
    (SOME (print_termtup ctxt))
    (terms_unify ctxt unif empty_env ==> sigma_unifies ctxt unif)

fun test_theorem_correctness ctxt unif gen_name gen =
  Spec_Check.check_gen ctxt
    ("Theorem correctness: "^gen_name)
    (gen_termtup gen)
    (SOME (print_termtup_unif ctxt unif))
    (terms_unify ctxt unif empty_env ==> theorem_correct ctxt unif)

fun test_theorem_correctness_var_term ctxt unif gen_name gen =
  Spec_Check.check_gen ctxt
    ("Theorem correctness unifying Var x with arbitrary term not containing x: "^gen_name)
    (gen_var_termtup gen)
    (SOME (print_termtup_unif ctxt unif))
    (terms_unify ctxt unif empty_env ==> theorem_correct ctxt unif)

fun test_theorem_correctness_vars_replaced ctxt unif gen_name gen =
  Spec_Check.check_gen ctxt
    ("Theorem correctness unifying t with t[Free/Var] (where all Vars are replaced by Frees): "^gen_name)
    (gen_termtup_repl_vars gen)
    (SOME (print_termtup ctxt))
    (terms_unify ctxt unif empty_env ==> theorem_correct ctxt unif)

fun test_occurs_check ctxt unif gen_name gen =
  Spec_Check.check_gen ctxt
    ("Occurs check stops unification: "^gen_name)
    (gen_occurs_clash_termtup gen)
    (SOME (print_termtup ctxt))
    (not o term_is_var o snd ==> not o terms_unify ctxt unif empty_env)

fun test_non_unif ctxt unif gen_name =
  test_termtup ctxt
    ("Non-unifiability (inequality \<Longrightarrow> non-unifiability): "^gen_name)
    (op <> ==> not o (terms_unify ctxt unif empty_env))

fun test_non_unif_rev ctxt unif gen_name =
  test_termtup ctxt
    ("Non-unifiability (non-unifiability \<Longrightarrow> inequality): "^gen_name)
    (not o (terms_unify ctxt unif empty_env) ==> op <>)

fun test_identical_unif ctxt unif gen_name gen =
  Spec_Check.check_gen ctxt
    ("Unifiability of identical terms:"^gen_name)
    (gen_identical_termtup gen)
    (SOME (print_termtup ctxt))
    (Property.property (terms_unify ctxt unif empty_env))

fun test_unif_var_term ctxt unif gen_name gen =
  Spec_Check.check_gen ctxt
    ("Unifiability of Var x with arbitrary term not containing x: "^gen_name)
    (gen_var_termtup gen)
    (SOME (print_termtup ctxt))
    (Property.property (terms_unify ctxt unif empty_env))
  
fun test_unif_vars_replaced ctxt unif gen_name gen =
  Spec_Check.check_gen ctxt
    ("Unifiability of t with t[Free/Var] (where all Vars are replaced by Frees): "^gen_name)
    (gen_termtup_repl_vars gen)
    (SOME (print_termtup ctxt))
    (Property.property (terms_unify ctxt unif empty_env))

end
