theory First_Steps
  imports
    Main
    "spec_check/src/Spec_Check"
begin



ML
\<open>
(* pretty-printing *)
val pwriteln = Pretty.writeln
val pretty_term = Syntax.pretty_term
fun pretty_terms ctxt trms =
  Pretty.block (Pretty.commas (map (pretty_term ctxt) trms))
fun pretty_cterm ctxt ctrm = pretty_term ctxt (Thm.term_of ctrm)
fun pretty_cterms ctxt ctrms =
  Pretty.block (Pretty.commas (map (pretty_cterm ctxt) ctrms))
fun pretty_thm ctxt thm = pretty_term ctxt (Thm.prop_of thm)
fun no_vars ctxt = Config.put show_question_marks false ctxt
fun pretty_thms ctxt thms =
  Pretty.block (Pretty.commas (map (pretty_thm ctxt) thms))
fun pretty_thms_no_vars ctxt thms =
  Pretty.block (Pretty.commas (map (pretty_thms ctxt) thms))
fun uncurry f (x, y) = f x y
fun flip f x y = f y x
fun flatten_tups [] = []
  | flatten_tups ((x,y)::xs) = x::y::flatten_tups xs
val pStr = Pretty.string_of

fun pretty_typ ctxt ty = Syntax.pretty_typ ctxt ty
fun pretty_typs ctxt tys = Pretty.block (Pretty.commas (map (pretty_typ ctxt) tys))
val tracingP = tracing o pStr
val term_pat_setup = let
val parser = Args.context -- Scan.lift Args.embedded_inner_syntax
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
    val print = apply2 (pretty_term ctxt) 
  in pretty_helper_p (print o get_trms) env
end
\<close>

setup \<open>term_pat_setup\<close>

ML\<open>
fun pretty_envs ctxt env=
  (pretty_tyenv ctxt (Envir.type_env env),
  pretty_env ctxt (Envir.term_env env));

fun pretty_ttups ctxt ts=
  let fun pretty_tup (x,y) =
        Pretty.block [Pretty.str "(",pretty_term ctxt x,Pretty.str ", ", pretty_term ctxt y,Pretty.str ")"]
      fun ttups [] = Pretty.str "[]"
        | ttups [x] = pretty_tup x 
        | ttups (x::xs) = Pretty.block [pretty_tup x, Pretty.str ", ",ttups xs]
  in Pretty.block [Pretty.str "[", ttups ts,Pretty.str "]"] end
\<close>

ML_file \<open>Log.ML\<close>

(*  F O U  *)
ML_file \<open>First_Order_Unification.ML\<close>

(*ML_file \<open>first_order_unification_code.ML\<close>*)

(* FOU test cases *)

(* implementing rule etc. *)
ML\<open>
(* FOU of the goal's ith subgoal with thm, returns NONE if non-unifiable or subgoal not existing *)
fun unifier_thm_goal ctxt goal thm i =
  let val _ = tracing ("Theorem: "^ (pretty_term ctxt (Thm.concl_of thm) |> Pretty.string_of) ^ "\nGoal: "^ (pretty_term ctxt ((Thm.prems_of goal |> flip nth (i-1) |> Logic.strip_imp_concl)) |> Pretty.string_of)) in
    SOME (Fou.first_order_unify ctxt
          (Thm.prems_of goal |> flip nth (i-1) |> Logic.strip_imp_concl, Thm.concl_of thm)
           (Envir.empty (Int.max (Thm.maxidx_of thm,Thm.maxidx_of goal))) |> fst) end
  handle Fou.Unif _  => NONE
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

(* CONTEXT missing for instantiation
fun fo_resolve0_tac rules i goal =
  let val unif_res = unif_thm @{context} goal rules i
    in biresolve0_tac (map (pair false) (fst unif_res)) i (snd unif_res) end
*)

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
(* declaring the unification method *)
declare [[unification = "first_order"]]

lemma "A \<Longrightarrow> A \<or> B"
  using [[unification = "higher_order"]]
  by (rule TrueI disjI1)

lemma "a = b \<Longrightarrow> f a = f (b::int)"
  by (rule arg_cong)

definition x1_def:"x1 = (4::int)"

theorem 413:"y = 4 \<Longrightarrow> y = 1 + (3::nat)" by simp
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

(*  H I N T S  *)

(* tactics for printing out current goal or subgoals, respectively, from cookbook *)
ML\<open>
fun my_print_tac ctxt thm =
  let val _ = tracingP (pretty_thm ctxt thm)
  in Seq.single thm end
fun my_print_tac_prems ctxt thm =
  let val _ = tracingP (pretty_terms ctxt (map Logic.strip_imp_concl (Thm.prems_of thm)))
  in Seq.single thm end
\<close>

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
  "Y \<equiv> Z \<Longrightarrow> X \<equiv> (0::nat) \<Longrightarrow> X + Y \<equiv> Y"
by simp

lemma ADD_SUC :
  "N = Suc Q \<Longrightarrow> P = Q + M \<Longrightarrow> N + M = Suc P"
by simp



ML \<open>val hints = Fou.gen_hint_list @{context}\<close>


declare [[show_types = true]]
declare  [[log_level=1000]]
ML\<open>
val no_eta_ctxt = Config.put eta_contract false @{context};
fun test_hunif (t1,t2) =
  let val ctxt = no_eta_ctxt
      val _ = pretty_terms ctxt [t1,t2] |> pwriteln
      val (sigma,thm) = Fou.first_order_unify_h ctxt (t1,t2) (Envir.empty 0)
      val (t1',t2') = (Envir.norm_term sigma t1,Envir.norm_term sigma t2)
      val _ = tracing "Unifying environment:"
      val _ = pretty_env ctxt (Envir.term_env sigma)
      val _ = pretty_tyenv ctxt (Envir.type_env sigma)
      val _ = tracing "Unifying theorem:"
      val _ = pretty_thm ctxt thm |> pwriteln
      val _ = tracing "Instantiated terms:"
      val _ = pwriteln (pretty_terms ctxt [t1',t2'])
  in () end
  handle Fou.Unif (tfail1,tfail2) => let val _ = tracing "Unification failed at terms: " in pretty_terms no_eta_ctxt [tfail1,tfail2] |> pwriteln end
       | Fou.Occurs_Check tfail1 =>  let val _ = tracing "Unification failed due to occurs check at terms: " in pretty_terms no_eta_ctxt [tfail1] |> pwriteln end
       (*| TUNIFY => let val _ = tracing "Type unification failed" in () end*)
\<close>
ML_file \<open>Test.ML\<close>


ML\<open>Gen_Term.term_fol (Gen_Term.def_sym_gen (1,1,0) 10) 5 10 (Random.new()) |> fst |> pretty_term @{context}\<close>

end