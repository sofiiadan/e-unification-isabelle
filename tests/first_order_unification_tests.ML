signature FIRST_ORDER_UNIFICATION_TESTS =
sig

  val tests_identical : (Context.generic, SpecCheck_Random.rand) Lecker.test
  val tests_identical_env : (Context.generic, SpecCheck_Random.rand) Lecker.test
  val tests_thm : (Context.generic, SpecCheck_Random.rand) Lecker.test
  val tests_replaced : (Context.generic, SpecCheck_Random.rand) Lecker.test
  val tests_symmetry : (Context.generic, SpecCheck_Random.rand) Lecker.test
  val generated_tests : (Context.generic, SpecCheck_Random.rand) Lecker.test

  val unit_tests_unifiable : (Context.generic, SpecCheck_Random.rand) Lecker.test
  val unit_tests_non_unifiable : (Context.generic, SpecCheck_Random.rand) Lecker.test

  val unit_tests_hints_non_recursive : (Context.generic, SpecCheck_Random.rand) Lecker.test
  val unit_tests_multiple_matching_hints : (Context.generic, SpecCheck_Random.rand) Lecker.test
  val unit_tests_hints_recursive : (Context.generic, SpecCheck_Random.rand) Lecker.test
  val unit_tests_hints : (Context.generic, SpecCheck_Random.rand) Lecker.test

  val unit_tests : (Context.generic, SpecCheck_Random.rand) Lecker.test

  val tests : (Context.generic, SpecCheck_Random.rand) Lecker.test

end

functor First_Order_Unification_Tests(P : sig
    val unify : Unification_Types.unifier
    val unify_hints : Unification_Types.unifier
    val params : {
      nv : int,
      ni : int,
      max_h : int,
      max_args : int
    }
  end) : FIRST_ORDER_UNIFICATION_TESTS =
struct

structure Prop = SpecCheck_Property
structure Gen = SpecCheck_Generator
open Unification_Tests_Base

val weights = (1, 1, 1, 0)

fun term_gen ctxt =
  let val {nv, ni, max_h, max_args} = P.params
  in term_gen' ctxt nv ni weights max_h max_args end

fun term_pair_gen ctxt =
  let val {nv, ni, max_h, max_args} = P.params
  in Unification_Tests_Base.term_pair_gen' ctxt nv ni weights max_h max_args end

(* standard unification *)
(** generated tests **)
(*** unification of identical terms ***)
fun tests_identical context r =
  let fun check_identical name unif context =
    let
      val ctxt = Context.proof_of context 
      val term_gen' = term_gen ctxt
    in
      check_thm (Gen.map (fn t => (t, t)) term_gen')
        ("Unifying identical terms with " ^ name) unif context
    end
  in
    Lecker.test_group context r [
      check_identical "unify" P.unify,
      check_identical "unify_hints" P.unify_hints
    ]
  end

fun tests_identical_env context r =
  let
    fun check_identical_env name unif context =
      let
        val ctxt = Context.proof_of context 
        val term_gen' = term_gen ctxt
      in
        check (Gen.map (fn t => (t, t)) term_gen')
          ("Unifying identical terms does not change environment with " ^ name)
          (Prop.==> (terms_unify unif context,
            (fn tp => unif context tp (Unification_Util.empty_envir tp) |> fst |> Envir.is_empty)))
          context
      end
  in
    Lecker.test_group context r [
      check_identical_env "unify" P.unify,
      check_identical_env "unify_hints" P.unify_hints
    ]
  end

(*** unification of randomly generated terms ***)
fun tests_thm context r =
  let
    fun check_thm name unif context =
      let
        val ctxt = Context.proof_of context 
        val term_pair_gen' = term_pair_gen ctxt
      in Unification_Tests_Base.check_thm term_pair_gen' name unif context end
    val context' =
      Config.put SpecCheck_Configuration.max_discard_ratio 100 (Context.proof_of context)
      |> Context.Proof
  in
    Lecker.test_group context' r [
      check_thm "unify" P.unify,
      check_thm "unify_hints" P.unify_hints
    ]
  end

fun tests_replaced context r =
  let fun check_replaced name unif context =
    let
      val ctxt = Context.proof_of context 
      val term_gen' = term_gen ctxt
      val unvarify = map_aterms (fn (Var ((n, i), T)) => Free (n ^ Int.toString i, T) | T => T)
    in
      check_thm (Gen.map (fn t => (t, unvarify t)) term_gen')
        ("Unifying terms with Var replaced by Free for " ^ name) unif context
    end
  in
    Lecker.test_group context r [
      check_replaced "unify" P.unify,
      check_replaced "unify_hints" P.unify_hints
    ]
  end

(**** symmetry ****)
fun tests_symmetry context r =
  let fun check_thm_symmetry name unif context =
    let
      val ctxt = Context.proof_of context 
      val term_pair_gen' = term_pair_gen ctxt
      val thm_correct' = thm_correct context unif
    in
      check term_pair_gen' ("Symmetry of " ^ name)
        (Prop.prop (fn tp =>  
          try thm_correct' tp = try thm_correct' (swap tp)))
        context
    end
  in
    Lecker.test_group context r [
      check_thm_symmetry "unify" P.unify,
      check_thm_symmetry "unify_hints" P.unify_hints
    ]
  end

fun generated_tests context r = 
  Lecker.test_group context r [
    tests_identical,
    tests_identical_env,
    tests_thm,
    tests_replaced,
    tests_symmetry
  ]

(** Unit tests **)
(*** unifiable ***)
fun unit_tests_unifiable context r =
  let 
    val tests = [
      (Var (("x", 0), TVar (("X", 0), [])), Var (("x", 0), TVar (("Y", 0), []))),
      (Var (("x", 0), TVar (("X", 0), [])), Var (("x", 0), TFree ("'a", []))),
      (Var (("x", 0), TVar (("X", 0), [])), Var (("y", 0), TVar (("X", 0), []))),
      (Var (("x", 0), TVar (("X", 0), [])), Free ("c", TFree ("'a", []))),
      (Var (("x", 0), TFree ("'a", [])), Free ("f", TVar (("X", 0), []))),
      (Var (("x", 0), TVar (("X", 0), [])), Free ("f", TFree ("'a", []))),
      (Var (("x", 0), TFree ("'a", [])), Free ("f", TFree ("'a", []))),
      (
        Free ("x", TFree ("'a", []) --> TVar (("X", 0), [])) $
          Free ("x", TVar (("Y", 0), [])),
        Free ("x", TVar (("Y", 0), []) --> TFree ("'b", [])) $
          Free ("x", TFree ("'a", []))
      ),
      (
        Free ("f", TVar (("X", 0), []) --> TVar (("Y", 0), [])) $
          Free ("c", TVar (("X", 0), [])),
        Free ("f", TVar (("X", 0), []) --> TVar (("Y", 0), [])) $
          Var (("x", 0), TVar (("X", 1), []))
      ),
      (
        Free ("f", [TVar (("A", 0), []), TVar (("B", 0), [])] ---> TFree ("c", [])) $
          Free ("a", TVar (("A", 0), [])) $
          Free ("b", TVar (("B", 0), [])),
        Free ("f", [TVar (("B", 0), []), TVar (("A", 0), [])] ---> TFree ("c", [])) $
          Free ("a", TVar (("B", 0), [])) $
          Free ("b", TVar (("A", 0), []))
      )
    ]
    fun check name unif context r = 
      check_list tests ("unifiable unit tests for " ^ name)
        (Prop.prop (thm_correct context unif)) context 
      |> K r
  in
    Lecker.test_group context r [
      check "unify" P.unify,
      check "unify_hints" P.unify_hints
    ]
  end

(*** non-unifiable ***)
fun unit_tests_non_unifiable context r =
  let 
    val unit_tests = [
      (Free("f", TFree("'a",[])), Free("f", TFree("'b",[]))),
      (Free("f", TFree("'a",[])), Free("g", TFree("'a",[])))
    ]
    fun check name unif context r = 
      check_list unit_tests ("non-unifiable unit tests for " ^ name)
        (Prop.prop (not o can (thm_correct context unif))) context
      |> K r
  in
    Lecker.test_group context r [
      check "unify" P.unify,
      check "unify_hints" P.unify_hints
    ]
  end

(* hint tests *)
(** non-recursive tests **)
fun unit_tests_hints_non_recursive context r =
  let 
    val ctxt = Proof_Context.set_mode Proof_Context.mode_schematic (Context.proof_of context)
    val hints = map (Skip_Proof.make_thm (Context.theory_of context) o Syntax.read_term ctxt) [
      "?x \<equiv> ?z \<Longrightarrow> ?y \<equiv> (0 :: nat) \<Longrightarrow> ?x + ?y \<equiv> ?z",
      "?x \<equiv> 1 \<Longrightarrow> ?y \<equiv> 1 \<Longrightarrow> ?x * ?y \<equiv> (1 :: nat)"
    ]
    val tests = map (apply2 (Syntax.read_term ctxt)) [
      ("1 :: nat", "1 + 0 :: nat"),
      ("1 :: nat", "?x + 0 :: nat"),
      ("1 :: nat", "?a * ?b :: nat")
    ]
    val check_hints = check_unit_tests_hints tests
  in
    Lecker.test_group context r [
      check_hints false [] "unify" P.unify,
      check_hints false [] "unify_hints without hints" P.unify_hints,
      check_hints true hints "unify_hints with hints" P.unify_hints
    ]
  end

(** multiple matching hints **)
fun unit_tests_multiple_matching_hints context r =
  let 
    val ctxt = Proof_Context.set_mode Proof_Context.mode_schematic (Context.proof_of context)
    val hints = map (Skip_Proof.make_thm (Context.theory_of context) o Syntax.read_term ctxt) [
      "Suc ?x \<equiv> 1",
      "?x \<equiv> 0 \<Longrightarrow> Suc ?x \<equiv> 1"
    ]
    val tests = map (apply2 (Syntax.read_term ctxt)) [
      ("Suc x :: nat", "1 :: nat")
    ]
    val check_hints = check_unit_tests_hints tests
  in
    Lecker.test_group context r [
      check_hints false [] "unify" P.unify,
      check_hints false [] "unify_hints without hints" P.unify_hints,
      check_hints false (tl hints) "unify_hints with wrong hints" P.unify_hints,
      check_hints true [hd hints] "unify_hints with correct hints" P.unify_hints,
      check_hints true hints "unify_hints with all hints" P.unify_hints,
      check_hints true (rev hints) "unify_hints with reversed hints order" P.unify_hints
    ]
  end

(** recursive hints **)
fun unit_tests_hints_recursive context r =
  let 
    val ctxt =
      Proof_Context.set_mode Proof_Context.mode_schematic (Context.proof_of context)
      |> Variable.declare_term @{term "f :: nat => nat"}
      |> Variable.declare_term @{term "g :: nat => nat"}
    val context' = Context.Proof ctxt
    val hints = map (Skip_Proof.make_thm (Context.theory_of context) o Syntax.read_term ctxt) [
        "?x \<equiv> ?z \<Longrightarrow> ?y \<equiv> (0 :: nat) \<Longrightarrow> ?x + ?y \<equiv> ?z",
        "?y \<equiv> ?x + ?z \<Longrightarrow> ?x + (Suc ?z) \<equiv> Suc ?y",
        "?x \<equiv> f (g 0) \<Longrightarrow> ?y \<equiv> g (f 0) \<Longrightarrow> f (g ?x) \<equiv> g (f ?y)",
        "?y \<equiv> f ?x \<Longrightarrow> ?x \<equiv> f (g 0) \<Longrightarrow> f (g ?x) \<equiv> g (f ?y)"
      ]
    val tests = map (apply2 (Syntax.read_term ctxt)) [
      ("1 :: nat", "(?x + 0) + 0 :: nat"),
      ("1 :: nat", "?x + (0 + 0) :: nat"),
      ("x + (Suc 0) :: nat", "Suc x :: nat"),
      ("f (g (f (g 0)))", "g (f (g (f 0)))"),
      ("f (g (f ((g 0) + 0)))", "g (f (f (f (g 0))))")
    ]
    val check_hints = check_unit_tests_hints tests
  in
    Lecker.test_group context' r [
      check_hints false [] "unify" P.unify,
      check_hints false [] "unify_hints without hints" P.unify_hints,
      check_hints true hints "unify_hints with hints" P.unify_hints
    ]
  end

fun unit_tests_hints context r = 
  Lecker.test_group context r [
    unit_tests_hints_non_recursive,
    unit_tests_multiple_matching_hints,
    unit_tests_hints_recursive
  ]

fun unit_tests context r = 
  Lecker.test_group context r [
    unit_tests_unifiable,
    unit_tests_non_unifiable,
    unit_tests_hints
  ]

fun tests context r = 
  Lecker.test_group context r [
    unit_tests,
    generated_tests
  ]

end