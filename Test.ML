signature TEST =
sig

  type unificationf = Context.generic -> term * term -> Envir.env -> (Envir.env * thm)
  type unif_test_gen = Context.generic -> unificationf -> string -> term Spec_Check_Gen_Types.gen
    -> Spec_Check_Random.rand -> Spec_Check_Random.rand

  val free_gen : int -> term Spec_Check_Gen_Types.gen
  val var_gen : int -> term Spec_Check_Gen_Types.gen
  val free_var_gen : int -> term Spec_Check_Gen_Types.gen

  val test_group : unif_test_gen -> unificationf -> string -> (int -> term Spec_Check_Gen_Types.gen) ->
    Spec_Check_Random.rand
  val test_group_idxs : unif_test_gen -> unificationf -> int list -> string -> (int -> term Spec_Check_Gen_Types.gen) ->
    Spec_Check_Random.rand
  val list_pos : Context.generic -> unificationf -> string -> (term * term) list ->
    (term * term) Seq.seq
  val list_neg : Context.generic -> unificationf -> string -> (term * term) list ->
    (term * term) Seq.seq
  val single_pos : Context.generic -> unificationf -> string -> (term * term) -> (term * term) Seq.seq
  val single_neg : Context.generic -> unificationf -> string -> (term * term) -> (term * term) Seq.seq

  val symmetry : unif_test_gen
  val sigma_unifies : unif_test_gen
  val sigma_unifies_var_term : unif_test_gen
  val sigma_unifies_vars_replaced : unif_test_gen
  val theorem_correctness : unif_test_gen
  val theorem_correctness_var_term : unif_test_gen
  val theorem_correctness_vars_replaced : unif_test_gen
  val non_unif : unif_test_gen
  val non_unif_rev : unif_test_gen
  val identical_unif : unif_test_gen
  val unif_var_term : unif_test_gen
  val unif_vars_replaced : unif_test_gen
  val noop : unif_test_gen
  val occurs_check : unif_test_gen

end

structure Test : TEST =
struct

open Utils
open Spec_Check_Property
infix ==>

type unificationf = Context.generic -> term * term -> Envir.env -> (Envir.env * thm)
type unif_test_gen = Context.generic -> unificationf -> string -> term Spec_Check_Gen_Types.gen -> Spec_Check_Random.rand ->
  Spec_Check_Random.rand

fun num_variants_gen nv = Spec_Check_Generator.lift nv
val index_gen = Spec_Check_Gen_Int.nonneg 10
fun aterm_args_gen nv weights h _ =
  Spec_Check_Gen_Base.zip (Spec_Check_Gen_Term.aterm' (num_variants_gen nv) index_gen weights)
      (Spec_Check_Gen_Int.nonneg (Int.max (0, 4-h)))

fun free_gen nv = Spec_Check_Gen_Term.term_tree (aterm_args_gen nv (0,1,0,0))
fun var_gen nv = Spec_Check_Gen_Term.term_tree (aterm_args_gen nv (0,0,1,0))
fun free_var_gen nv = Spec_Check_Gen_Term.term_tree (aterm_args_gen nv (0,3,1,0))

val empty_env = Envir.empty 0

fun test_with test unif gen_name gen n =
  test (Context.the_generic_context ()) unif (gen_name^", max. index "^Int.toString n) (gen n)

fun test_group test unif gen_name gen =
  fold
    I
    (map (test_with test unif gen_name gen) [1,5,10])
    (Spec_Check_Random.new ())

fun test_group_idxs test unif idxs gen_name gen =
  fold
    (fn test => test)
    (map (test_with test unif gen_name gen) idxs)
    (Spec_Check_Random.new ())

fun print_term ctxt t =
  Pretty.string_of (pretty_term ctxt t)

fun print_termtup ctxt (t1,t2) =
  pretty_terms (Context.proof_of ctxt) [t1,t2]

fun print_termtup_unif ctxt unif (t1,t2) =
  let
    val (env,thm) = unif ctxt (t1,t2) empty_env
    val pctxt = Context.proof_of ctxt
  in
    Pretty.chunks [
      print_termtup ctxt (t1,t2),
      Pretty.block [Pretty.str "Type Environment: ", pretty_tyenv_p pctxt (Envir.type_env env)],
      Pretty.block [Pretty.str "Term Environment: ", pretty_env_p pctxt (Envir.term_env env)],
      Pretty.block [Pretty.str "Theorem: ", pretty_thm pctxt thm],
      Pretty.block [Pretty.str "Unified terms: ", pretty_terms pctxt
        [Envir.norm_term env t1,Envir.norm_term env t2]]
    ]
  end handle _ =>
        Pretty.block [Pretty.str "Unification failed, terms: ", print_termtup ctxt (t1,t2)]

val is_var = fn Var _ => true | _ => false

(*replaces all Vars by Frees with the same name and type*)
fun replace_vars x =
  case x of
    Var ((x,_),tya) => Free (x,tya)
    |f$x => (replace_vars f) $ (replace_vars x)
    |t => t

(*increases the indices of all Vars by n*)
fun incr_idx n =
   fn Var ((name,idx),typ) => Var ((name,idx+n),typ)
   |  Abs (s,T,t) => (Abs(s,T,incr_idx n t))
   |  t1 $ t2 => incr_idx n t1 $ incr_idx n t2
   |  t => t

(*generates a term and typechecks it*)
fun gen_term_typed ctxt tgen rand =
  let
    val (t,r) = tgen rand
    val pctxt = Context.proof_of ctxt
  in
    (Syntax.check_term
      (Proof_Context.set_mode Proof_Context.mode_schematic (Context.the_local_context ())) t,r)
    handle _ =>
      let val _ =
        Log.debug pctxt tracing ("Generated term could not be properly typed: "^print_term pctxt t)
      in gen_term_typed ctxt tgen r end
  end

(*generates a tuple of (t1,t2)*)
fun gen_termtup ctxt tgen rand =
  let
    val (t1,rand1) = gen_term_typed ctxt tgen rand
    val (t2,rand2) = gen_term_typed ctxt tgen rand1
  in ((t1,incr_idx (Term.maxidx_of_term t1 +1) t2),rand2) end

(*generates a tuple of (Var,t)*)
fun gen_var_termtup ctxt tgen rand =
  let val (t,rand) = gen_term_typed ctxt tgen rand
  in ((Var(("AVAR",1001),TVar(("'atype",1001),[])),t),rand) end

(*generates a tuple of (t,t') where t' is t with every Var replaced by a Free*)
fun gen_termtup_repl_vars ctxt tgen rand =
  let val (t,rand) = gen_term_typed ctxt tgen rand
  in ((t,replace_vars t),rand) end

(*generates a tuple of (t,t)*)
fun gen_identical_termtup ctxt tgen rand =
  let val (t,rand) = gen_term_typed ctxt tgen rand
  in ((t,t),rand) end

(*generates a tuple of (Var,t) where Var occurs in t*)
fun gen_occurs_clash_termtup ctxt tgen rand =
  let val (t,rand) = gen_term_typed ctxt tgen rand
      val var = hd (Term.add_vars t [])
  in ((Var var,t),rand) end

(*checks if two terms match and have the same size*)
fun terms_match_size_eq ctxt (t1,t2) =
  let val _ = Pattern.match (Proof_Context.theory_of ctxt) (t1,t2) (Vartab.empty,Vartab.empty)
  in size_of_term t1 = size_of_term t2 end handle _ => false

(*checks if terms can be unified by unif*)
fun terms_unify ctxt unif envir ts =
  let val _ = unif ctxt ts envir
  in true end handle _ => false

(*checks if terms can be unified by unif, raises exception if not*)
fun terms_unify_exn ctxt unif envir ts =
  let val _ = unif ctxt ts envir
  in true end

(*checks if the environment resulting from unif (t1,t2) unifies t1 and t2*)
fun sigma_unif ctxt unif (t1,t2) =
  let val (sigma,_) = unif ctxt (t1,t2) empty_env
  in Envir.norm_term sigma t1 = Envir.norm_term sigma t2 end

(*checks if the environment resulting from unif ts is unchanged*)
fun sigma_unchanged ctxt unif ts =
  let val (sigma,_) = unif ctxt ts empty_env
  in Envir.is_empty sigma end

val terms_from_thm =
  (fn (Const ("Pure.eq",_) $ t1 $ t2) => (t1,t2)) o Thm.concl_of

(*checks if the theorem resulting from unif (t1,t2) unifies t1 and t2*)
fun theorem_correct ctxt unif (t1,t2) =
  let
    val (sigma,thm) = unif ctxt (t1,t2) empty_env
    val (t1',t2') = (Envir.norm_term sigma t1,Envir.norm_term sigma t2)
    val (lhs,rhs) = terms_from_thm thm
    val pctxt = (Context.proof_of ctxt)
  in
    (terms_match_size_eq pctxt (lhs,t1') andalso terms_match_size_eq pctxt (rhs,t2'))
    orelse (terms_match_size_eq pctxt (lhs,t2') andalso terms_match_size_eq pctxt (rhs,t1'))
  end handle _ => false

fun list_pos ctxt unif name l =
  Spec_Check.check_list (print_termtup ctxt) l name
    (prop (terms_unify_exn ctxt unif empty_env)) (Context.proof_of ctxt)

fun list_neg ctxt unif name l =
  Spec_Check.check_list (print_termtup ctxt) l name
    (prop (not o terms_unify ctxt unif empty_env))
    (Context.proof_of ctxt)

fun single_pos ctxt unif name ts =
  Spec_Check.check_list (print_termtup ctxt) [ts] name
    (prop (terms_unify_exn ctxt unif empty_env))
    (Context.proof_of ctxt)

fun single_neg ctxt unif name ts =
  Spec_Check.check_list (print_termtup ctxt) [ts] name
    (prop (not o terms_unify ctxt unif empty_env))
    (Context.proof_of ctxt)

val shrink_termtup = Spec_Check_Shrink.product Spec_Check_Shrink.term Spec_Check_Shrink.term

fun test_termtup ctxt unif name prop gen =
  Spec_Check.check_shrink (print_termtup_unif ctxt unif) shrink_termtup
    (gen_termtup ctxt gen) name prop (Context.proof_of ctxt)

fun symmetry ctxt unif gen_name gen =
  let val terms_unify' = terms_unify ctxt unif empty_env
  in
    test_termtup ctxt unif ("Symmetry test: "^gen_name)
      (prop
        (fn (t1,t2) => (terms_unify' (t1,t2) andalso terms_unify' (t2,t1))
         orelse (not (terms_unify' (t1,t2)) andalso not (terms_unify' (t2,t1)))))
      gen
  end

fun theorem_correctness ctxt unif gen_name gen =
  Spec_Check.check_shrink (print_termtup_unif ctxt unif) shrink_termtup (gen_termtup ctxt gen)
    ("Theorem correctness: "^gen_name)
    (terms_unify ctxt unif empty_env ==> theorem_correct ctxt unif)
    (Context.proof_of ctxt)

fun theorem_correctness_var_term ctxt unif gen_name gen =
  Spec_Check.check_shrink (print_termtup_unif ctxt unif) shrink_termtup (gen_var_termtup ctxt gen)
    ("Theorem correctness unifying Var x with arbitrary term not containing x: "^gen_name)
    (terms_unify ctxt unif empty_env ==> theorem_correct ctxt unif)
    (Context.proof_of ctxt)

fun theorem_correctness_vars_replaced ctxt unif gen_name gen =
  Spec_Check.check_shrink (print_termtup ctxt) shrink_termtup (gen_termtup_repl_vars ctxt gen)
    ("Theorem correctness unifying t with t[Free/Var] (where all Vars are replaced by Frees): "^gen_name)
    (terms_unify ctxt unif empty_env ==> theorem_correct ctxt unif)
    (Context.proof_of ctxt)

fun sigma_unifies ctxt unif gen_name =
  test_termtup ctxt unif
    ("Sigma unifies terms: "^gen_name)
    (terms_unify ctxt unif empty_env ==> sigma_unif ctxt unif)

fun sigma_unifies_var_term ctxt unif gen_name gen =
  Spec_Check.check_shrink (print_termtup_unif ctxt unif) shrink_termtup (gen_var_termtup ctxt gen)
    ("Sigma unifies Var x with arbitrary term not containing x: "^gen_name)
    (terms_unify ctxt unif empty_env ==> sigma_unif ctxt unif)
    (Context.proof_of ctxt)

fun sigma_unifies_vars_replaced ctxt unif gen_name gen =
  Spec_Check.check_shrink (print_termtup ctxt) shrink_termtup (gen_termtup_repl_vars ctxt gen)
    ("Sigma unifies terms with replaced Vars: "^gen_name)
    (terms_unify ctxt unif empty_env ==> sigma_unif ctxt unif)
    (Context.proof_of ctxt)

fun non_unif ctxt unif gen_name =
  test_termtup ctxt unif
    ("Non-unifiability (inequality \<Longrightarrow> non-unifiability): "^gen_name)
    (op <> ==> not o (terms_unify ctxt unif empty_env))

fun non_unif_rev ctxt unif gen_name =
  test_termtup ctxt unif
    ("Non-unifiability (non-unifiability \<Longrightarrow> inequality): "^gen_name)
    (not o (terms_unify ctxt unif empty_env) ==> op <>)

fun identical_unif ctxt unif gen_name gen =
  Spec_Check.check_shrink (print_termtup ctxt) shrink_termtup
    (gen_identical_termtup ctxt gen)
    ("Unifiability of identical terms:"^gen_name)
    (prop (terms_unify ctxt unif empty_env))
    (Context.proof_of ctxt)

fun unif_var_term ctxt unif gen_name gen =
  Spec_Check.check_shrink (print_termtup ctxt) shrink_termtup
    (gen_var_termtup ctxt gen)
    ("Unifiability of Var x with arbitrary term not containing x: "^gen_name)
    (prop (terms_unify ctxt unif empty_env))
    (Context.proof_of ctxt)

fun unif_vars_replaced ctxt unif gen_name gen =
  Spec_Check.check_shrink (print_termtup ctxt) shrink_termtup
    (gen_termtup_repl_vars ctxt gen)
    ("Unifiability of t with t[Free/Var] (where all Vars are replaced by Frees): "^gen_name)
    (prop (terms_unify ctxt unif empty_env))
    (Context.proof_of ctxt)

fun noop ctxt unif gen_name gen =
  Spec_Check.check_shrink (print_termtup ctxt) shrink_termtup (gen_identical_termtup ctxt gen)
    ("Envir unchanged when unifying identical terms: "^gen_name)
    (prop (sigma_unchanged ctxt unif)) (Context.proof_of ctxt)

fun occurs_check ctxt unif gen_name gen =
  Spec_Check.check_shrink (print_termtup ctxt) shrink_termtup (gen_occurs_clash_termtup ctxt gen)
    ("Occurs check stops unification: "^gen_name)
    (not o is_var o snd ==> not o terms_unify ctxt unif empty_env)
    (Context.proof_of ctxt)

end
