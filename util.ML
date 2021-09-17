(*TODO: signature*)
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

fun show_unif_result ctxt (t1,t2) (env, thm) =
  (@{log} ctxt (K "Unification results:");
  @{log} ctxt (fn _ => pretty_env ctxt env |> Pretty.string_of);
  @{log} ctxt (fn _ => pretty_thm ctxt thm |> Pretty.string_of))

(*We store a binder as ((name, typ), fresh Free variable), where the fresh free variable is used
as a replacement for the corresponding bound variable, for example, when creating theorems
underneath abstractions.*)
type binder = (string * typ) * term

fun new_binder context name T =
  let
    val ctxt = Context.proof_of context
    val (name', ctxt') = yield_singleton Variable.variant_fixes name ctxt
  in (Context.Proof ctxt', ((name, T), Free (name', T))) end

fun binder_free binders = snd o nth binders

(*replace all Bounds by corresponding Frees*)
fun replace_binders binders tp = let val bvars = map snd binders
  in apply2 (subst_bounds o pair bvars) tp end

fun maxidx_of_terms ts = fold (Integer.max o maxidx_of_term) ts ~1

fun empty_envir (t1, t2) = Envir.empty (maxidx_of_terms [t1, t2])

fun show_test_result ctxt tp unif =
  let
    val pctxt = Context.proof_of ctxt
    val sigma = unif ctxt tp (empty_envir tp)
  in show_unif_result pctxt tp sigma end

fun norm_thm_types ctxt (Envir.Envir {tyenv, ...}) thm =
  let
    val prop = Thm.prop_of thm
    val norm_type = Envir.norm_type tyenv
    fun prep_type_entry x = (x, Thm.ctyp_of ctxt (norm_type (TVar x)))
    val type_inst = Term.add_tvars prop [] |> map prep_type_entry
    val inst = (type_inst, [])
  in Thm.instantiate inst thm end

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
  in Thm.instantiate inst thm end

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
        (@{log Logger.DEBUG} ctxt
          (fn _ => Pretty.block [
              Pretty.str "Failed to unify types ",
              pretty_types ctxt (map (Envir.norm_type tyenv) [T, U])
            ] |> Pretty.string_of);
        raise Unification_Types.UNIF)
      end

end

