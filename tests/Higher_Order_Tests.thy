theory Higher_Order_Tests
imports
  Unification_Tests_Base
begin

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
  structure First_Order_Tests = First_Order_Tests(Test_Params)
\<close>

ML\<open>
  Theory.setup (
    ML_Antiquotation.inline_embedded \<^binding>\<open>term_pat\<close>
    (Args.term_pattern >> (ML_Syntax.atomic o ML_Syntax.print_term)))
\<close>

declare[[show_types=true]]

ML\<open>
  val (t, s) = (
      (* @{term_pat "(?x :: ?'X, ?y :: ?'Y, ?z :: ?'Z)"},
      @{term_pat "((f :: ?'Y \<Rightarrow> ?'X) (?y :: ?'Y), (g :: ?'Z \<Rightarrow> ?'Y) (?z :: ?'Z), c :: ?'C)"} *)
      @{term_pat "(?y :: ?'Y, ?y :: ?'Y, ?z :: ?'Z)"},
      @{term_pat "(?x :: ?'X, ?z :: ?'Z, ?c :: ?'C)"}
      (* @{term_pat "(?z :: ?'Z, ?y :: ?'Y, ?x :: ?'X)"},
      @{term_pat "(?y :: ?'Y, ?x :: ?'X, ?c :: ?'C)"} *)
      (* @{term_pat "(?v_2.1::?'a2 \<Rightarrow> ?'b2) (v_2::?'a2)"}, *)
      (* @{term_pat "(f::?'X) (a::?'a) (b::?'b)"}, *)
      (* @{term_pat "(f::?'Y) (a::?'b) (b::?'b)"} *)
      (* Var (("x", 0), TFree ("'a", []) --> TVar (("X", 0), [])) $ Var (("x", 0), TVar (("Y", 0), [])), *)
      (* Var (("x", 0), TVar (("Y", 0), []) --> TFree ("'b", [])) $ Var (("x", 0), TFree ("'a", [])) *)
    )
  val env =
    First_Order_Unification.unify (Context.the_generic_context ()) (t,s) Envir.init
  val _ = Unification_Util.pretty_env @{context} (fst env) 
    |> Pretty.writeln
  val thm = (snd env)
  val b = Unification_Util.norm_thm @{context} (fst env) (snd env)
  (* val env =
    Unify.unifiers ((Context.the_generic_context ()), Envir.init, [(t,s)])
    |> Seq.hd
    |> fst *)
  (* val env = *)
    (* Envir.update ((("'x", 0), TVar (("'X", 0), [])), @{term_pat "?z :: ?'Z"}) env *)
  (* val _ = 
    env
    |> Unification_Util.pretty_env @{context}
    |> Pretty.writeln
  val (t', s') =
    apply2 (Envir.norm_term env) (t, s)
    |> apply2 (Syntax.pretty_term @{context})
    |> apply2 Pretty.writeln *)
\<close>

(* ML\<open>
  val (t, s) = (
      @{term_pat "(?x :: ?'X \<Rightarrow> ?'R)"},
      @{term_pat "(?y :: ?'Y \<Rightarrow> ?'R)"}
    )
  val env = 
    Unify.unifiers ((Context.the_generic_context ()), Envir.init, [(t,s)]) |> Seq.hd 
    (* |> fst
    |> Unification_Util.pretty_env @{context}
    |> Pretty.writeln *)
  val env2 = 
    Unify.smash_unifiers (Context.the_generic_context ()) [(t,s)] Envir.init
    |> Seq.hd
    |> Unification_Util.pretty_env @{context}
    |> Pretty.writeln

  (*returns correct unifier for (t, s')*)
  val t' = (Var (("y", 0), TFree ("'b", [])))
  val s' = (Var (("x", 0), TFree ("'b", [])))
  val env' = 
    Unify.unifiers ((Context.the_generic_context ()), Envir.init, [(t', s')]) |> Seq.hd
    (* |> fst
    |> Unification_Util.pretty_env @{context}
    |> Pretty.writeln *)
\<close> *)

(* ML\<open>
  val tp = (@{term_pat "\<lambda> (z :: ?'Z). (?x :: ?'Z \<Rightarrow> ?'B) z"},
            @{term_pat "\<lambda> (z :: ?'A). (?x :: ?'A \<Rightarrow> ?'B) z"})
  val tp' = (@{term_pat "x :: 'X"}, @{term_pat "x :: ?'Y"})
  val _ = Pattern.unify (Context.the_generic_context ()) tp Envir.init
    |> Unification_Util.pretty_env @{context}
    |> Pretty.writeln
  val _ = Pattern.unify (Context.the_generic_context ()) tp' Envir.init
    |> Unification_Util.pretty_env @{context}
    |> Pretty.writeln
\<close> *)

ML\<open>
  structure Prop = SpecCheck_Property
  open Unification_Tests_Base
  open Unification_Util
  val unify_hints = Higher_Order_Pattern_Unification.unify_hints
  val unify = Higher_Order_Pattern_Unification.unify
\<close>

(*Higher-order-exclusive tests*)
ML\<open>
  val (t1,t2) = (@{term_pat "\<lambda> x. f x"}, @{term_pat "\<lambda> x. f x"});
  trace_test_result (Context.the_generic_context ()) (t1, t2) unify_hints
\<close>

ML\<open>
  val (t1,t2) = (@{term_pat "\<lambda>x. \<lambda>y. (x::nat)"},@{term_pat "\<lambda>y. \<lambda>x. y"});
  trace_test_result (Context.the_generic_context ()) (t1,t2) unify_hints\<close>

ML\<open>
  val (t1,t2) = (@{term_pat "\<lambda>x. r x ?Y"},@{term_pat "\<lambda>x. r x ?Y"});
  trace_test_result (Context.the_generic_context ()) (t1,t2) unify_hints\<close>

ML\<open>
  val (t1,t2) = (@{term_pat "\<lambda>x. (x, (\<lambda> y. (y, \<lambda> z. ?x)))"},@{term_pat "\<lambda>x. (x, (\<lambda> y. (y, \<lambda> z. f)))"});
  trace_test_result (Context.the_generic_context ()) (t1,t2) unify_hints\<close>

lemma [hints]:"X\<equiv>(0::nat) \<Longrightarrow> Y\<equiv>Z \<Longrightarrow> X + Y \<equiv>Z"
by linarith
ML\<open>
  val (t1,t2) = (@{term_pat "\<lambda>x. (\<lambda>y. 0 + 1::nat)"},@{term_pat "\<lambda>x. (\<lambda>y. 1::nat)"});
  trace_test_result (Context.the_generic_context ()) (t1,t2) unify_hints\<close>

ML\<open>
  val (t1,t2) = (@{term_pat "(\<lambda>x. 0 + Z + x::nat)"},@{term_pat "(\<lambda>x. Z + x::nat)"});
  trace_test_result (Context.the_generic_context ()) (t1,t2) unify_hints\<close>

ML\<open>
  val (t1,t2) = (@{term_pat "\<lambda>x. (\<lambda>y. 0 + Suc ?x::nat)"},@{term_pat "\<lambda>x. (\<lambda>y. 3::nat)"});
  trace_test_result (Context.the_generic_context ()) (t1,t2) unify_hints\<close>

consts
  A :: "(nat \<Rightarrow> nat) \<times> nat \<Rightarrow> nat"
  B :: "nat \<times> nat \<Rightarrow> nat"
  C :: "nat"

ML\<open>
  val (t1,t2) = (@{term_pat "\<lambda>u. B (?x,u)"},@{term_pat "\<lambda>v. B (C,v)"});
  trace_test_result (Context.the_generic_context ()) (t1,t2) unify_hints\<close>

ML\<open>
  val (t1,t2) = (@{term_pat "A (\<lambda>u. B (?x,u),C)"},@{term_pat "A (\<lambda>v. B (C,v),?y)"});
  trace_test_result (Context.the_generic_context ()) (t1,t2) unify_hints\<close>

ML\<open>
  val (t1,t2) = (@{term_pat "A (\<lambda>u. B (?x,C), C)"},@{term_pat "id (A (\<lambda>u. ?y, C+0))"});
  trace_test_result (Context.the_generic_context ()) (t1,t2) unify_hints\<close>

ML\<open>
  val (t1,t2) = (@{term_pat "\<lambda>x. 0 + x::nat"},@{term_pat "\<lambda>x. x::nat"});
  trace_test_result (Context.the_generic_context ()) (t1,t2) unify_hints\<close>


end
