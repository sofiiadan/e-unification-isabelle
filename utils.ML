structure Utils =
struct

fun pretty_terms ctxt = Pretty.list "" "" o map (Syntax.pretty_term ctxt)

fun pretty_thm ctxt thm = Syntax.pretty_term ctxt (Thm.prop_of thm)

fun pretty_helper_p aux prems =
  prems |> map aux
        |> map (fn (s1, s2) => Pretty.block [s1, Pretty.str " := ", s2])
        |> Pretty.enum "," "[" "]"

fun pretty_helper_env aux env =
  env |> Vartab.dest
      |> map aux
      |> map (fn (s1, s2) => Pretty.block [s1, Pretty.str " := ", s2])
      |> Pretty.enum "," "[" "]"
      |> Pretty.writeln

fun pretty_helper_env_p aux env =
  env |> Vartab.dest
      |> map aux
      |> map (fn (s1, s2) => Pretty.block [s1, Pretty.str " := ", s2])
      |> Pretty.enum "," "[" "]"

fun pretty_tyenv ctxt tyenv =
  let
    fun get_typs (v, (s, T)) = (TVar (v, s), T)
    val print = apply2 (Syntax.pretty_typ ctxt)
  in pretty_helper_env (print o get_typs) tyenv
end

fun pretty_tyenv_p ctxt tyenv =
  let
    fun get_typs (v, (s, T)) = (TVar (v, s), T)
    val print = apply2 (Syntax.pretty_typ ctxt)
  in pretty_helper_env_p (print o get_typs) tyenv
end

fun pretty_env ctxt env =
  let
    fun get_trms (v, (T, t)) = (Var (v, T), t)
    val print = apply2 (Syntax.pretty_term ctxt)
  in pretty_helper_env (print o get_trms) env
end

fun pretty_env_p ctxt env =
  let
    fun get_trms (v, (T, t)) = (Var (v, T), t)
    val print = apply2 (Syntax.pretty_term ctxt)
  in pretty_helper_env_p (print o get_trms) env
end

fun pretty_prems ctxt env =
  let
    fun get_trms ((v, T), t) = (Var (v, T), t)
    val print = apply2 (Syntax.pretty_term ctxt)
  in pretty_helper_p (print o get_trms) env
end

fun pretty_hint ctxt (_,prems,thm) =
  Pretty.block
    [pretty_prems ctxt prems, Pretty.str " \<Longrightarrow> ", Syntax.pretty_term ctxt (Thm.concl_of thm)]

val term_pat_setup =
  let val parser = Args.context -- Scan.lift Args.embedded_inner_syntax
      fun term_pat (ctxt, str) =
        str |> Proof_Context.read_term_pattern ctxt
            |> ML_Syntax.print_term
            |> ML_Syntax.atomic
  in
    ML_Antiquotation.inline @{binding "term_pat"} (parser >> term_pat)
  end

fun trace_unif_result ctxt (t1,t2) (env,thm) =
  let
    val _ = Logger.info ctxt tracing "Unification results:"
    val _ = Logger.info ctxt (tracing o Pretty.string_of o pretty_env_p ctxt o Envir.term_env) env
    val _ = Logger.info ctxt (tracing o Pretty.string_of o pretty_tyenv_p ctxt o Envir.type_env) env
    val _ = Logger.info ctxt (tracing o Pretty.string_of o pretty_thm ctxt) thm
    val _ = Logger.info ctxt (tracing o Pretty.string_of o pretty_terms ctxt)
      [Envir.norm_term env t1,Envir.norm_term env t2]
  in () end

fun trace_test_result ctxt ts unif =
  let
    val pctxt = Context.proof_of ctxt
    val sigma = unif ctxt ts (Envir.empty 0)
  in trace_unif_result pctxt ts sigma end

fun norm_thm ctxt env =
  let 
    val tyenv = Envir.type_env env
    val tyenv_dest = Vartab.dest tyenv
    (*normalise the types in the type environment*)
    val tenv_dest =
      Envir.term_env env
      |> Vartab.map (Envir.norm_type tyenv |> apfst |> K)
      |> Vartab.dest
    fun prep_trm ctxt (x, (T, t)) = ((x, T), Thm.cterm_of ctxt t)
    fun prep_ty ctxt (x, (S, ty)) = ((x, S), Thm.ctyp_of ctxt ty)
    val inst = (map (prep_ty ctxt) tyenv_dest, map (prep_trm ctxt) tenv_dest)
  in Drule.instantiate_normalize inst end

end

