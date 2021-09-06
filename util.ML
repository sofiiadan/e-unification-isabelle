structure Unification_Util =
struct

fun pretty_terms ctxt = Pretty.list "" "" o map (Syntax.pretty_term ctxt)

fun pretty_types ctxt = Pretty.list "" "" o map (Syntax.pretty_typ ctxt)

fun pretty_thm ctxt = Syntax.pretty_term ctxt o Thm.prop_of

fun pretty_helper_env aux env =
  env |> Vartab.dest
      |> map aux
      |> map (fn (s1, s2) => Pretty.block [s1, Pretty.str " := ", s2])
      |> Pretty.list "[" "]"

fun pretty_tyenv ctxt tyenv =
  let
    fun get_typs (v, (s, T)) = (TVar (v, s), T)
    val print = apply2 (Syntax.pretty_typ ctxt)
  in pretty_helper_env (print o get_typs) tyenv
end

fun pretty_tenv ctxt tenv =
  let
    fun get_trms (v, (T, t)) = (Var (v, T), t)
    val print = apply2 (Syntax.pretty_term ctxt)
  in pretty_helper_env (print o get_trms) tenv
end

fun pretty_env ctxt (Envir.Envir {tyenv, tenv,...}) =
  Pretty.list "(" ")" [pretty_tyenv ctxt tyenv, pretty_tenv ctxt tenv]

fun trace_unif_result ctxt (t1,t2) (env,thm) =
  (Logger.info ctxt writeln "Unification results:";
  Logger.info ctxt (writeln o Pretty.string_of o pretty_tenv ctxt o Envir.term_env) env;
  Logger.info ctxt (writeln o Pretty.string_of o pretty_tyenv ctxt o Envir.type_env) env;
  Logger.info ctxt (writeln o Pretty.string_of o pretty_thm ctxt) thm;
  Logger.info ctxt (writeln o Pretty.string_of o pretty_terms ctxt)
    [Envir.norm_term env t1, Envir.norm_term env t2])

fun trace_test_result ctxt ts unif =
  let
    val pctxt = Context.proof_of ctxt
    val sigma = unif ctxt ts Envir.init
  in trace_unif_result pctxt ts sigma end


local
  fun prep_type ctxt (x, (S, ty)) = ((x, S), Thm.ctyp_of ctxt ty)
in

fun norm_thm_types ctxt (Envir.Envir {tyenv, ...}) thm =
  let 
    val prop = Thm.prop_of thm
    val norm_type = Envir.norm_type tyenv
    fun prep_type_entry x = (x, Thm.ctyp_of ctxt (norm_type (TVar x)))
    val type_inst = Term.add_tvars prop [] |> map prep_type_entry
    val inst = (type_inst, [])
  in Drule.instantiate_normalize inst thm end

(* fun norm_thm_types ctxt (Envir.Envir {tyenv, ...}) =
  let 
    val norm_type = Envir.norm_type tyenv
    fun norm_type_entry _ (S, T) = (S, norm_type T)
    (*normalise the type environment*)
    val tyenv_dest = Vartab.map norm_type_entry tyenv |> Vartab.dest
    val inst = (map (prep_type ctxt) tyenv_dest, [])
  in Drule.instantiate_normalize inst end *)
(* 
fun norm_thm ctxt (env as Envir.Envir {tyenv, tenv,...}) =
  let 
    val norm_type = Envir.norm_type tyenv
    val norm_term = Envir.norm_term env
    fun norm_term_entry _ (T, t) = (norm_type T, norm_term t)
    (*normalise the types in the term environment*)
    val tenv_dest = Vartab.map norm_term_entry tenv |> Vartab.dest
    fun norm_type_entry _ (S, T) = (S, norm_type T)
    (*normalise the type environment*)
    val tyenv_dest = Vartab.map norm_type_entry tyenv |> Vartab.dest
    fun prep_term ctxt (x, (T, t)) = ((x, T), Thm.cterm_of ctxt t)
    val inst = (map (prep_type ctxt) tyenv_dest, map (prep_term ctxt) tenv_dest)
  in Drule.instantiate_normalize inst end *)

fun norm_thm ctxt (env as Envir.Envir {tyenv,...}) thm =
  let 
    val prop = Thm.prop_of thm
    val norm_type = Envir.norm_type tyenv
    val norm_term = Envir.norm_term env
    fun prep_type_entry x = (x, Thm.ctyp_of ctxt (norm_type (TVar x)))
    val type_inst = Term.add_tvars prop [] |> map prep_type_entry
    fun prep_term_entry (x as (n, T)) = ((n, norm_type T), Thm.cterm_of ctxt (norm_term (Var x)))
    val term_inst = Term.add_vars prop [] |> map prep_term_entry
    val inst = (type_inst, term_inst)
  in Drule.instantiate_normalize inst thm end

end

fun unify_types context (T, U) (env as Envir.Envir {maxidx, tenv, tyenv}) =
  if T = U then env
  else
    let
      val thy = Context.theory_of context
      val (tyenv', maxidx') = Sign.typ_unify thy (T, U) (tyenv, maxidx)
    in Envir.Envir {maxidx = maxidx', tenv = tenv, tyenv = tyenv'} end
    handle Type.TUNIFY =>
      let val ctxt = Context.proof_of context;
      in 
        (Logger.debug ctxt
          (fn _ => Pretty.block [
              Pretty.str "Failed to unify types ",
              pretty_types ctxt (map (Envir.norm_type tyenv) [T, U])
            ]
            |> Pretty.writeln)
          ();
        raise Pattern.Unif)
      end

end

