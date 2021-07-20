theory First_Steps
  imports
    Main
    Spec_Check2.Spec_Check
begin


ML\<open>
  fun pretty_helper_p aux prems =
  prems |> map aux
        |> map (fn (s1, s2) => Pretty.block [s1, Pretty.str " := ", s2])
        |> Pretty.enum "," "[" "]"

fun pretty_prems ctxt env =
  let
    fun get_trms (v, (T, t)) = (Var (v, T), t)
    val print = apply2 (Syntax.pretty_term ctxt) 
  in pretty_helper_p (print o get_trms) env
end

fun pretty_hint ctxt (_,prems,thm) =
  Pretty.block
    [pretty_prems ctxt prems,
     Pretty.str " \<Longrightarrow> ",
     Syntax.pretty_term ctxt (Thm.concl_of thm)]
\<close>



ML
\<open>
(* pretty-printing *)
val pwriteln = Pretty.writeln
val pretty_term = Syntax.pretty_term
fun pretty_terms ctxt trms =
  Pretty.block (Pretty.commas (map (pretty_term ctxt) trms))
fun pretty_thm ctxt thm = pretty_term ctxt (Thm.prop_of thm)
fun pretty_thms ctxt thms =
  Pretty.block (Pretty.commas (map (pretty_thm ctxt) thms))


fun pretty_typ ctxt ty = Syntax.pretty_typ ctxt ty
fun pretty_typs ctxt tys = Pretty.block (Pretty.commas (map (pretty_typ ctxt) tys))
val term_pat_setup =
  let val parser = Args.context -- Scan.lift Args.embedded_inner_syntax
      fun term_pat (ctxt, str) =
        str |> Proof_Context.read_term_pattern ctxt
            |> ML_Syntax.print_term
            |> ML_Syntax.atomic
  in
    ML_Antiquotation.inline @{binding "term_pat"} (parser >> term_pat)
  end

fun pretty_helper aux env =
  env |> Vartab.dest
      |> map aux
      |> map (fn (s1, s2) => Pretty.block [s1, Pretty.str " := ", s2])
      |> Pretty.enum "," "[" "]"
      |> pwriteln

fun pretty_helper_p aux env =
  env |> Vartab.dest
      |> map aux
      |> map (fn (s1, s2) => Pretty.block [s1, Pretty.str " := ", s2])
      |> Pretty.enum "," "[" "]"

fun pretty_tyenv ctxt tyenv =
  let
    fun get_typs (v, (s, T)) = (TVar (v, s), T)
    val print = apply2 (pretty_typ ctxt)
  in pretty_helper (print o get_typs) tyenv
end

fun pretty_tyenv_p ctxt tyenv =
  let
    fun get_typs (v, (s, T)) = (TVar (v, s), T)
    val print = apply2 (pretty_typ ctxt)
  in pretty_helper_p (print o get_typs) tyenv
end

fun pretty_env ctxt env =
  let
    fun get_trms (v, (T, t)) = (Var (v, T), t)
    val print = apply2 (pretty_term ctxt) 
  in pretty_helper (print o get_trms) env
end

fun pretty_env_p ctxt env =
  let
    fun get_trms (v, (T, t)) = (Var (v, T), t)
    val print = apply2 (Syntax.pretty_term ctxt) 
  in pretty_helper_p (print o get_trms) env
end


fun flip f x y = f y x
\<close>

setup \<open>term_pat_setup\<close>



ML_file \<open>Log.ML\<close>

(*  F O U  *)
ML_file \<open>First_Order_Unification.ML\<close>

(* implementing rule etc. *)
ML\<open>
(* FOU of the goal's ith subgoal with thm, returns NONE if non-unifiable or subgoal not existing *)
fun unifier_thm_goal ctxt goal thm i =
  let val _ = tracing ("Theorem: "^ (pretty_term ctxt (Thm.concl_of thm) |> Pretty.string_of) ^ "\nGoal: "^ (pretty_term ctxt ((Thm.prems_of goal |> flip nth (i-1) |> Logic.strip_imp_concl)) |> Pretty.string_of)) in
    SOME (HUnif.first_order_unify (Context.the_generic_context ())
          (Thm.prems_of goal |> flip nth (i-1) |> Logic.strip_imp_concl, Thm.concl_of thm)
           (Envir.empty (Int.max (Thm.maxidx_of thm,Thm.maxidx_of goal))) |> fst) end
  handle Unif  => NONE
       | Type.TUNIFY => NONE
       | Subscript   => NONE

(*Fou.Unif _ =>
          let val _ = tracing "Unification failed" in NONE end
       | Subscript  =>
          let val _ =
            tracing ("Subscript raised, Theorem: "
             ^ (pretty_thm ctxt thm |> Pretty.string_of)
              ^ "\n\t\t  Goal: "
               ^ (pretty_thm ctxt goal |> Pretty.string_of)) in NONE end*)

(* converts environment into destructed lists of term and type mappings *)
fun env_lists (Envir.Envir {tenv,tyenv,...}) ctxt =
let fun ctyp (i_n,(sort,ty)) = ((i_n,sort),Thm.ctyp_of ctxt ty)
    fun ctrm (i_n,(typ,t)) = ((i_n,typ),Thm.cterm_of ctxt t)
in (map ctyp (Vartab.dest tyenv), map ctrm (Vartab.dest tenv)) end;

(* FOU of the goal with the first rule applicable.
   returns instantiated ([rule],goal), or ([],goal) if none applicable *)
fun unif_thm _ goal [] _ = ([],goal) |
    unif_thm ctxt goal (rule::rules) i =
      (case unifier_thm_goal ctxt goal rule i of
        NONE => unif_thm ctxt goal rules i |
        SOME env =>
          let val _ = tracing ("Unification succeeded, Envir: ")
              val _ = pretty_env ctxt (Envir.term_env env)
              val _ = pretty_tyenv ctxt (Envir.type_env env) in
                    ([(Thm.instantiate (env_lists env ctxt) rule)],
                      (Thm.instantiate (env_lists env ctxt) goal)) end)

(* Resolution using FOU *)
fun fo_resolve_tac ctxt rules i goal =
  let val (rules,goal) = unif_thm ctxt goal rules i
    in biresolve_tac ctxt (map (pair false) rules) i goal end

(* Resolution with elimination rules using FOU *)
fun fo_eresolve_tac ctxt rules i goal = 
  let val (rules,goal) = unif_thm ctxt goal rules i
    in biresolve_tac ctxt (map (pair true) rules) i goal end

(* Forward tactic using FOU *)
fun fo_forward_tac ctxt rules = 
  fo_resolve_tac ctxt (map make_elim rules) THEN' assume_tac ctxt

(* Resolution with deletion of assumption using FOU *)
fun fo_dresolve_tac ctxt rules = fo_eresolve_tac ctxt (map make_elim rules)

fun fo_ares_tac ctxt rules = assume_tac ctxt ORELSE' fo_resolve_tac ctxt rules;

fun fo_solve_tac ctxt rules = fo_resolve_tac ctxt rules THEN_ALL_NEW assume_tac ctxt;

(* tactic for intro using FOU *)
fun fo_match_tac ctxt rules i goal =
  let val (rules,goal) = unif_thm ctxt goal rules i
    in bimatch_tac ctxt (map (pair false) rules) i goal end;

(* tactic for elim using FOU *)
fun fo_ematch_tac ctxt rules i goal =
  let val (rules,goal) = unif_thm ctxt goal rules i
    in bimatch_tac ctxt (map (pair true) rules) i goal end;
\<close>

ML\<open>

val unification = Attrib.setup_config_string @{binding "unification"} (K "higher_order");

fun get_current_unif ctxt =
    Config.get ctxt unification |> (fn "first_order" => 1 | _ => 0);

(**)
fun xrule_meth meths =
  Scan.lift (Scan.optional (Args.parens Parse.nat) 0)
  -- Attrib.thms >>
    (fn (n, ths) => fn ctxt => (nth meths (get_current_unif ctxt)) ctxt n ths
     handle Subscript => raise Fail "Invalid unification method");
(**)

local
fun gen_rule_tac tac ctxt rules facts =
  (fn i => fn st =>
    if null facts then tac ctxt rules i st
    else
      Seq.maps (fn rule => (tac ctxt o single) rule i st)
        (Drule.multi_resolves (SOME ctxt) facts rules))
  THEN_ALL_NEW Goal.norm_hhf_tac ctxt;

fun gen_arule_tac tac ctxt j rules facts =
  EVERY' (gen_rule_tac tac ctxt rules facts :: replicate j (assume_tac ctxt));

fun gen_some_rule_tac tac ctxt arg_rules facts = SUBGOAL (fn (goal, i) =>
  let
    val rules =
      if not (null arg_rules) then arg_rules
      else flat (Context_Rules.find_rules ctxt false facts goal);
  in Method.trace ctxt rules; tac ctxt rules facts i end);

fun meth tac x y = METHOD (HEADGOAL o tac x y);
fun meth' tac x y z = METHOD (HEADGOAL o tac x y z);

in
(* neu *)
val _ = match_tac;
val rule_tac = gen_rule_tac resolve_tac;
val rule_tac_fo = gen_rule_tac fo_resolve_tac;

val rule = meth rule_tac;

val some_rule_tac = gen_some_rule_tac rule_tac;
val some_rule_tac_fo = gen_some_rule_tac rule_tac_fo;

val some_rule = meth some_rule_tac;
val some_rule_fo = meth some_rule_tac_fo;


val erule = meth' (gen_arule_tac eresolve_tac);
val erule_fo = meth' (gen_arule_tac fo_eresolve_tac);
val drule = meth' (gen_arule_tac dresolve_tac);
val drule_fo = meth' (gen_arule_tac fo_dresolve_tac);
val frule = meth' (gen_arule_tac forward_tac);
val frule_fo = meth' (gen_arule_tac fo_forward_tac);
end;

(* weiter oben in Method.ML *)
fun intro ctxt ths = SIMPLE_METHOD' (CHANGED_PROP o REPEAT_ALL_NEW (match_tac ctxt ths));
fun intro_fo ctxt ths = SIMPLE_METHOD' (CHANGED_PROP o REPEAT_ALL_NEW (fo_match_tac ctxt ths));
fun elim ctxt ths = SIMPLE_METHOD' (CHANGED_PROP o REPEAT_ALL_NEW (ematch_tac ctxt ths));
fun elim_fo ctxt ths = SIMPLE_METHOD' (CHANGED_PROP o REPEAT_ALL_NEW (fo_ematch_tac ctxt ths));

fun intro_elim tacs =
  (Attrib.thms >>
    (fn ths => fn ctxt => (nth tacs (get_current_unif ctxt)) ctxt ths
     handle Subscript => raise Fail "Invalid unification method"));

(*********)

val _ = Theory.setup
 (Method.setup \<^binding>\<open>intro\<close> (intro_elim [intro,intro_fo])
    "repeatedly apply introduction rules" #>
  Method.setup \<^binding>\<open>elim\<close> (intro_elim [elim,elim_fo])
    "repeatedly apply elimination rules" #>
  Method.setup \<^binding>\<open>rule\<close>
    (Attrib.thms >>
    (fn ths => fn ctxt => (nth [some_rule,some_rule_fo] (get_current_unif ctxt)) ctxt ths
     handle Subscript => raise Fail "Invalid unification method")) "apply some intro/elim rule" #>
  Method.setup \<^binding>\<open>erule\<close> (xrule_meth [erule,erule_fo]) "apply rule in elimination manner (improper)" #>
  Method.setup \<^binding>\<open>drule\<close> (xrule_meth [drule,drule_fo]) "apply rule in destruct manner (improper)" #>
  Method.setup \<^binding>\<open>frule\<close> (xrule_meth [frule,frule_fo]) "apply rule in forward manner (improper)");
\<close>

(* tests for FOU-tactics *)
declare [[unification = "first_order"]]

lemma "A \<Longrightarrow> A \<or> B"
  using [[unification = "higher_order"]]
  by (rule TrueI disjI1)

lemma "a = b \<Longrightarrow> f a = f (b::int)"
  by (rule arg_cong)

definition x1_def:"x1 = (4::int)"

theorem 413:"y = 4 \<Longrightarrow> y = 1 + 3" by simp
theorem 4132: "y = 4 \<Longrightarrow> y = 1 + 3" by simp

lemma "x1 = 1 + 3"
  apply (rule 413 4132)
  by (rule x1_def)

lemma "True \<and> True"
  by rule+

lemma "A \<longrightarrow> A"
  by (intro imp_refl)

lemma "True \<or> False"
  by rule+

lemma "A \<or> B \<Longrightarrow> B \<or> A"
  apply (elim disjE)
  apply (erule disjI2)
  by (erule disjI1)

lemma "A \<or> B \<Longrightarrow> B \<or> A"
  by (erule Meson.disj_comm)

lemma "A \<and> B \<Longrightarrow> B \<and> A"
  apply rule
  apply (drule conjunct2) defer
  by (drule conjunct1)

theorem l1:"\<lbrakk>A; C\<rbrakk> \<Longrightarrow> A" by simp

lemma "\<lbrakk>A; B\<rbrakk> \<Longrightarrow> A"
  by (erule l1)

lemma "(\<forall>x. f x) \<Longrightarrow> f x"
  by (erule allE)

lemma "a = b \<Longrightarrow> f a = f b"
  by (elim arg_cong)

lemma "(\<not>G \<longrightarrow> \<not>F) \<longrightarrow> (F \<longrightarrow> G)"
  apply (rule impI)+
  apply (rule case_split[of G]) defer 
  apply (rule FalseE)
  apply (rule notE[of F])
  by (erule impE)

(*  Hints  *)

named_theorems hints

lemma SUCS :
  "X \<equiv> 0 \<Longrightarrow> Suc X \<equiv> 1"
  "X \<equiv> 1 \<Longrightarrow> Suc X \<equiv> 2"
  "X \<equiv> 2 \<Longrightarrow> Suc X \<equiv> 3"
  "X \<equiv> 3 \<Longrightarrow> Suc X \<equiv> 4"
  "X \<equiv> 4 \<Longrightarrow> Suc X \<equiv> 5"
  "X \<equiv> 5 \<Longrightarrow> Suc X \<equiv> 6"
  "X \<equiv> 6 \<Longrightarrow> Suc X \<equiv> 7"
  "X \<equiv> 7 \<Longrightarrow> Suc X \<equiv> 8"
  "X \<equiv> 8 \<Longrightarrow> Suc X \<equiv> 9"
  "X \<equiv> 9 \<Longrightarrow> Suc X \<equiv> 10"
by linarith+

lemma NULL_MINUS :
  "X \<equiv> Y \<Longrightarrow> X - Y \<equiv> (0::nat)"
by simp

lemma ADD_COMM :
  "X \<equiv> Y \<Longrightarrow> X + Y \<equiv> Y + (X ::nat)"
by linarith

lemma ADD_ZERO_ZERO:
  "X \<equiv> 0 \<Longrightarrow> Y \<equiv> 0 \<Longrightarrow> X + Y \<equiv> (0::nat)"
by simp

lemma MULT_ONE :
  "X \<equiv> 1 \<Longrightarrow> Y \<equiv> 1 \<Longrightarrow> X * Y \<equiv> (1::nat)"
by simp

lemma ADD_ZERO:
  "Y \<equiv> Z \<Longrightarrow> X \<equiv> (0::nat) \<Longrightarrow> Y + X \<equiv> Z"
by simp

lemma ZERO_ADD:
  "Y \<equiv> Z \<Longrightarrow> X \<equiv> (0::nat) \<Longrightarrow> X + Y \<equiv> Z"
by simp

lemma ADD_SUC:
  "N \<equiv> Suc Q \<Longrightarrow> P \<equiv> Q + M \<Longrightarrow> N + M \<equiv> Suc P"
by simp

lemma Suc1:
  "Y \<equiv> 2 \<Longrightarrow> X \<equiv> 1 \<Longrightarrow> Suc X \<equiv> Y" by linarith

ML\<open>
  val (_, make_thm_cterm) =
  Context.>>>
    (Context.map_theory_result (Thm.add_oracle (Binding.make ("skip", \<^here>), I)));
fun make_thm thy (t1,t2) = make_thm_cterm (Thm.global_cterm_of thy (Const ("Pure.eq",type_of t1 --> type_of t2 --> propT) $ t1 $ t2))
fun make_thm' thy t = make_thm_cterm (Thm.global_cterm_of thy t)\<close>

declare[[eta_contract=false]]
declare[[unify_trace_failure=true]]

ML\<open>
  val cong = Thm.axiom @{theory} "Pure.combination";
  val theorem_ff = make_thm @{theory} (@{term_pat "f ::'a"},@{term_pat "f::'a"});
  val theorem_00 = make_thm @{theory} (@{term_pat "0 ::nat"},@{term_pat "0::nat"});
  val theorem_00_foralled = forall_intr_vars theorem_00;
  val res = cong OF [theorem_ff,theorem_00]
\<close>


consts t1 ::"nat \<Rightarrow> bool"  t2 ::"nat \<Rightarrow> bool" 
declare[[eta_contract=false]]
declare[[unify_trace_failure=false]]
ML\<open>
   val t3 = @{term_pat "\<lambda>x. t1 x"};
   val t4 = @{term_pat "\<lambda>y. t2 y"};
   val b = @{term_pat "?x::nat"};
   val abstr = Thm.axiom @{theory} "Pure.abstract_rule";
   val thm = make_thm @{theory} (@{term_pat "f::nat\<Rightarrow>bool"} $ b,@{term_pat "g::nat\<Rightarrow>bool"} $ b);
   val thm_forall = forall_intr_list [Thm.cterm_of @{context} @{term_pat "?x::nat"}] thm;
   val _ = Seq.empty;

   val thm_t1 = Thm.prems_of abstr |> hd;
   val thm_t2 = Thm.prop_of thm_forall;
   val env = Pattern.unify (Context.the_generic_context ()) (thm_t1,thm_t2) (Envir.empty 0);
   val _ = env |>Envir.term_env |> pretty_env @{context};
   val [th1,th2] = map (Envir.norm_term env) [thm_t1,thm_t2];

   Thm.biresolution NONE false [(false,thm_forall)] 1 abstr |> Seq.list_of;
   Thm.concl_of thm_forall;
   Thm.prop_of thm_forall;
   Thm.biresolution;
   (*abstr OF [thm_foralled]*);

   val abstr_inst = Drule.infer_instantiate @{context} [(("f",0),Thm.cterm_of @{context} @{term_pat "\<lambda>x. f x"}),(("g",0),Thm.cterm_of @{context} @{term_pat "\<lambda>x. g x"})] abstr
   val of_thm = abstr_inst OF [thm]
\<close>

ML\<open>
  fun unif_abstr ctxt thm var env =
  let
    val pctxt = Context.proof_of ctxt
    val abstr_prem_t = Thm.prems_of abstr |> hd
    val thm_forall = forall_intr_list [Thm.cterm_of pctxt var] thm
    val thm_forall_t = Thm.concl_of thm_forall
    val unif_env = Pattern.unify ctxt (abstr_prem_t,thm_forall_t) env
    val _ = pretty_env pctxt (Envir.term_env unif_env)
    val inst_list = map
      (fn (idxn,(_,t)) => (idxn,Thm.cterm_of pctxt (Envir.norm_term unif_env t)))
      (Envir.term_env unif_env |> Vartab.dest)
    val abstr_inst = Drule.infer_instantiate pctxt inst_list abstr
  in
    abstr_inst OF [thm]
  end;

val x = unif_abstr (Context.the_generic_context ()) thm @{term_pat "?x::nat"} (Envir.empty 0)

\<close>



lemma H1: \<open>(\<And>x. f x \<equiv> g x) \<Longrightarrow> \<lambda>x. f x \<equiv> \<lambda>x. g x\<close>
  by auto

context
  assumes H2: \<open>\<And>x. f x \<equiv> g x\<close>
begin


ML\<open>
  Thm.concl_of @{thm H2};
  Thm.concl_of thm_forall
\<close>


ML \<open>abstr OF [thm_forall];
    @{thm H1} OF @{thms H2}\<close>
end

ML\<open>
  val (t1,t2) = (@{term_pat "(\<lambda>x. x 3) f"},@{term_pat "(f::nat\<Rightarrow>nat) 3"});
  val _ = pretty_terms @{context} [t1,t2] |> pwriteln;
  val env = Pattern.unify (Context.the_generic_context ()) (t1,t2) (Envir.empty 0);
  val _ = pretty_env @{context} (Envir.term_env env)
  val _ = pretty_tyenv @{context} (Envir.type_env env)
\<close>
(* HIGHER ORDER *)
ML_file "pattern_copy.ML"
declare[[eta_contract=false]]
ML\<open>
  val (env,thm) = HUnif.first_order_unify_h (Context.the_generic_context ()) (@{term_pat "\<lambda>x. f x"},@{term_pat "\<lambda>x. f x"}) (Envir.empty 0);
  pretty_env @{context} (Envir.term_env env);
  pretty_thm @{context} thm |> pwriteln;
  pretty_terms @{context} [@{term_pat "\<lambda>x. f x"},@{term_pat "\<lambda>x. f x"}]
\<close>
lemma [hints]:"X\<equiv>(0::nat) \<Longrightarrow> Y\<equiv>Z \<Longrightarrow> X + Y \<equiv>Z"
by linarith

lemma [hints]:"X\<equiv>1 \<Longrightarrow> Suc X \<equiv> 2"
by linarith
  
ML\<open>
  val (env,thm) = PatternH.h_unify (Context.the_generic_context ()) (@{term_pat "0 + 2::nat"},@{term_pat "Suc 1::nat"}) (Envir.empty 0);
  pretty_env @{context} (Envir.term_env env);
  pretty_thm @{context} thm |> pwriteln
\<close>

ML\<open>
  val (env,thm) = PatternH.h_unify (Context.the_generic_context ()) (@{term_pat "\<lambda>x. r x ?Y"},@{term_pat "\<lambda>x. r x ?Y"}) (Envir.empty 0);
  pretty_env @{context} (Envir.term_env env);
  pretty_thm @{context} thm |> pwriteln
\<close>

ML\<open>
  val (env,thm) = PatternH.h_unify (Context.the_generic_context ()) (@{term_pat "\<lambda>x. (\<lambda>y. 0+(1::nat))"},@{term_pat "\<lambda>x. (\<lambda>y. (1::nat))"}) (Envir.empty 0);
  pretty_env @{context} (Envir.term_env env);
  pretty_thm @{context} thm |> pwriteln
\<close>

ML\<open>
  val (env,thm) = PatternH.h_unify (Context.the_generic_context ()) (@{term_pat "(\<lambda>x. (0+Z)+x::nat    )"},@{term_pat "(\<lambda>x. Z +x::nat)"}) (Envir.empty 0);
  pretty_env @{context} (Envir.term_env env);
  pretty_thm @{context} thm |> pwriteln
\<close>



(*Typen in ctxt speichern/binders an try_hints übergeben*)
ML\<open>
  val (env,thm) = PatternH.h_unify (Context.the_generic_context ()) (@{term_pat "\<lambda>x. (\<lambda>x. 0+x::nat)"},@{term_pat "\<lambda>x. (\<lambda>x. x::nat)"}) (Envir.empty 0);
  pretty_env @{context} (Envir.term_env env);
  pretty_thm @{context} thm |> pwriteln
\<close>

ML\<open>
  val (env,thm) = PatternH.h_unify (Context.the_generic_context ()) (@{term_pat "\<lambda>x. \<lambda>y. (x::nat)"},@{term_pat "\<lambda>x. \<lambda>y. x"}) (Envir.empty 0);
  pretty_env @{context} (Envir.term_env env);
  pretty_thm @{context} thm |> pwriteln;
\<close>


consts
  A :: "(nat \<Rightarrow> nat) \<times> nat \<Rightarrow> nat" 
  B :: "nat \<times> nat \<Rightarrow> nat"
  C :: "nat"
  f :: "nat \<Rightarrow> nat"


ML\<open>
  val (t1,t2) = (@{term_pat "A (\<lambda>u. B (?x,u),C)"},@{term_pat "A (\<lambda>v. B (?y,v),C)"});
  val (env,thm) = PatternH.h_unify (Context.the_generic_context ()) (t1,t2) (Envir.empty 0);
  pretty_env @{context} (Envir.term_env env);
  pretty_thm @{context} thm |> pwriteln
\<close>

ML\<open>
  val (t1,t2) = (@{term_pat "\<lambda>u. B (?x,u)"},@{term_pat "\<lambda>v. B (?y,v)"});
  val (env,thm) = PatternH.h_unify (Context.the_generic_context ()) (t1,t2) (Envir.empty 0);
  pretty_env @{context} (Envir.term_env env);
  pretty_thm @{context} thm |> pwriteln
\<close>




datatype Expr = EVar int | EOp Expr Expr

fun eval_expr :: "Expr \<Rightarrow> int" where
  "eval_expr (EVar i) = i"
| "eval_expr (EOp ex1 ex2) = (eval_expr ex1) + (eval_expr ex2)"

fun simpl :: "Expr \<Rightarrow> Expr" where
  "simpl (EVar i) = EVar i"
| "simpl (EOp ex1 ex2) = EVar (eval_expr (simpl ex1) + eval_expr (simpl ex2))"

lemma soundness :
  "P (eval_expr (simpl x)) \<Longrightarrow> P (eval_expr x)"
sorry

lemma "3 + 4 \<equiv> (4::int) + 3"
by linarith

lemma h_base : "a \<equiv> EVar i \<Longrightarrow> eval_expr a \<equiv> i"
by simp

lemma h_add : "a \<equiv> EOp x y \<Longrightarrow> m \<equiv> eval_expr x \<Longrightarrow> n \<equiv> eval_expr y \<Longrightarrow> eval_expr a \<equiv> m + n"
by simp

ML\<open>
  val t1 = @{term_pat "eval_expr ?y"};
  val t2 = @{term_pat "a + (b + c) ::int"}
\<close>

declare [[log_level=600]]

ML\<open>
  val (env,thm) = PatternH.h_unify (Context.the_generic_context ()) (t1,t2) (Envir.empty 0);
  pretty_env @{context} (Envir.term_env env);
  pretty_thm @{context} thm |> pwriteln;
  pretty_terms @{context} [Envir.norm_term env t1,Envir.norm_term env t2];
\<close>

ML\<open>
  val (t1,t2) = (@{term_pat "(a::nat) ^ 3"},@{term_pat "(0+(?x::nat))^3"});
  val (env,thm) = PatternH.h_unify (Context.the_generic_context ()) (t1,t2) (Envir.empty 0);
  pretty_env @{context} (Envir.term_env env);
  pretty_thm @{context} thm |> pwriteln;
  pretty_terms @{context} [Envir.norm_term env t1,Envir.norm_term env t2];
\<close>
end