signature UNIFICATION_UTIL =
sig

  (* pretty-printing *)
  val pretty_types : Proof.context -> typ list -> Pretty.T
  val pretty_terms : Proof.context -> term list -> Pretty.T
  val pretty_thm : Proof.context -> thm -> Pretty.T

  val pretty_tyenv : Proof.context -> Type.tyenv -> Pretty.T
  val pretty_tenv : Proof.context -> Envir.tenv -> Pretty.T
  val pretty_env : Proof.context -> Envir.env -> Pretty.T

  (* sequences *)
  (*raises exception if sequence is empty and returns the sequence otherwise*)
  val seq_try : exn -> 'a Seq.seq -> 'a Seq.seq
  val seq_is_empty : 'a Seq.seq -> bool

  (* terms and environments *)
  val maxidx_of_terms : term list -> int
  (*returns empty environment with maxidx set to maximum of given terms*)
  val empty_envir : term * term -> Envir.env

  (* binders *)
  (*We store a binder as ((name, typ), fresh Free variable), where the fresh free variable is used
  as a replacement for the corresponding bound variable, for example, when creating theorems
  underneath abstractions.*)
  type binder = (string * typ) * term
  val new_binder : Proof.context -> string -> typ -> Proof.context * binder
  (*returns free variable corresponding to the given binder*)
  val binder_free : binder list -> int -> term
  (*replaces all binders by their corresponding free variable in the given term*)
  val replace_binders : binder list -> term -> term

  (* instantiations *)
  (*normalise and abstract over a given variable*)
  val abstract : Proof.context -> string -> term -> Envir.env * thm -> Envir.env * thm
  val norm_thm_types : Proof.context -> Envir.env -> thm -> thm
  val norm_thm : Proof.context -> Envir.env -> thm -> thm

 (*raises Unification_Base.UNIF on failure*)
  val unify_types : Proof.context -> typ * typ -> Envir.env -> Envir.env

  val log_unif_result : Proof.context -> term * term -> Envir.env * thm -> unit
  val log_unif_results : Proof.context -> term * term -> Unification_Base.unifier -> unit
  val log_unif_results' : int -> Proof.context  -> term * term -> Unification_Base.unifier -> unit

end

structure Unification_Util : UNIFICATION_UTIL =
struct

(* pretty-printing *)
local
val pretty_term = Syntax.pretty_term
val pretty_type = Syntax.pretty_typ

fun pretty_env_aux show_entry =
  Vartab.dest
  #> map show_entry
  #> Pretty.list "[" "]"

fun pretty_env_entry show (s, t) = Pretty.block [show s, Pretty.str " := ", show t]

val pretty_record =
  map (fn (key, entry) => Pretty.block [Pretty.str key, Pretty.str "=", entry])
  #> Pretty.enum "," "{" "}"
in

fun pretty_types ctxt = Pretty.block o Pretty.commas o map (pretty_type ctxt)
fun pretty_terms ctxt = Pretty.block o Pretty.commas o map (pretty_term ctxt)
fun pretty_thm ctxt = Syntax.pretty_term ctxt o Thm.prop_of

fun pretty_tyenv ctxt =
  let
    val show_entry = pretty_env_entry (pretty_type ctxt)
    fun get_typs (v, (s, T)) = (TVar (v, s), T)
  in pretty_env_aux (show_entry o get_typs) end

fun pretty_tenv ctxt =
  let
    val show_entry = pretty_env_entry (pretty_term ctxt)
    fun get_trms (v, (T, t)) = (Var (v, T), t)
  in pretty_env_aux (show_entry o get_trms) end

fun pretty_env ctxt (Envir.Envir {maxidx, tyenv, tenv}) =
  pretty_record [
    ("maxidx", Pretty.str (string_of_int maxidx)),
    ("tyenv", pretty_tyenv ctxt tyenv),
    ("tenv", pretty_tenv ctxt tenv)
  ]

end

(* sequences *)
fun seq_try exn sq = case Seq.pull sq of
    NONE => raise exn
  | SOME (v, sq') => Seq.cons v sq'

fun seq_is_empty sq = is_none (Seq.pull sq)

(* terms and environments *)
fun maxidx_of_terms ts = fold (Integer.max o maxidx_of_term) ts ~1

fun empty_envir (t1, t2) = Envir.empty (maxidx_of_terms [t1, t2])

(* binders *)
type binder = (string * typ) * term

fun new_binder ctxt name T =
  let val (name', ctxt') = yield_singleton Variable.variant_fixes name ctxt
  in (ctxt', ((name, T), Free (name', T))) end

fun binder_free binders = snd o nth binders

(*replace all Bounds by corresponding Frees*)
fun replace_binders binders t = let val bvars = map snd binders
  in subst_bounds (bvars, t) end

(* instantiations *)
fun abstract ctxt name bvar (env as Envir.Envir {tyenv,...}, thm) =
  let
    val bvar' = map_types (Envir.norm_type tyenv) bvar
    val thm' = Unification_Base.abstract_rule name (Thm.cterm_of ctxt bvar') thm
  in (env, thm') end

(*collect and normalise TVars of a term*)
fun collect_norm_types ctxt tyenv t =
  let
    val norm_type = Envir.norm_type tyenv
    fun prep_type_entry x = (x, Thm.ctyp_of ctxt (norm_type (TVar x)))
  in
    fold_types (fold_atyps (fn (TVar v) => TVars.add (prep_type_entry v) | _ => I)) t
    |> TVars.build
  end

(*collect and normalise Vars of a term*)
fun collect_norm_terms ctxt (env as Envir.Envir {tyenv,...}) t =
  let
    val norm_type = Envir.norm_type tyenv
    val norm_term = Envir.norm_term env
    fun prep_term_entry (x as (n, T)) = ((n, norm_type T), Thm.cterm_of ctxt (norm_term (Var x)))
  in
    fold_aterms (fn (Var v) => Vars.add (prep_term_entry v) | _ => I) t
    |> Vars.build
  end

(*normalise types of a theorem*)
fun norm_thm_types ctxt (Envir.Envir {tyenv, ...}) thm =
  let
    val prop = Thm.prop_of thm
    val type_inst = collect_norm_types ctxt tyenv prop
    val inst = (type_inst, Vars.empty)
  in Thm.instantiate inst thm end

(*normalise a theorem*)
fun norm_thm ctxt (env as Envir.Envir {tyenv,...}) thm =
  let
    val prop = Thm.prop_of thm
    val type_inst = collect_norm_types ctxt tyenv prop
    val term_inst = collect_norm_terms ctxt env prop
    val inst = (type_inst, term_inst)
  in Thm.instantiate inst thm end

fun unify_types ctxt (T, U) (env as Envir.Envir {maxidx, tenv, tyenv}) =
  if T = U then env
  else
    let val (tyenv', maxidx') = Sign.typ_unify (Proof_Context.theory_of ctxt) (T, U) (tyenv, maxidx)
    in Envir.Envir {maxidx = maxidx', tenv = tenv, tyenv = tyenv'} end
    handle Type.TUNIFY =>
      (@{log Logger.DEBUG} ctxt
        (fn _ => Pretty.block [
            Pretty.str "Failed to unify types ",
            pretty_types ctxt (map (Envir.norm_type tyenv) [T, U])
          ] |> Pretty.string_of);
      raise Unification_Base.UNIF)

fun log_unif_result ctxt _ (env, thm) =
  (@{log} ctxt (K "Environment:");
  @{log} ctxt (fn _ => pretty_env ctxt env |> Pretty.string_of);
  @{log} ctxt (K "Theorem:");
  @{log} ctxt (fn _ => pretty_thm ctxt thm |> Pretty.string_of))

fun log_unif_results ctxt tp unif =
  let val res = unif ctxt tp (empty_envir tp) |> Seq.list_of
  in fold (log_unif_result ctxt tp #> K) res () end

fun log_unif_results' n ctxt tp unif =
  let val res = unif ctxt tp (empty_envir tp) |> Seq.take n |> Seq.list_of
  in fold (log_unif_result ctxt tp #> K) res () end

end

