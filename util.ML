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
  (*During unification, when going underneath an abstraction, we store a binder as
  ((name, typ), fresh Free variable), where the fresh free variable is used as a replacement for the
  corresponding bound variable, for example, when having to create a reflexivity theorem for the
  binder.*)
  type binder = (string * typ) * term
  val new_binder : Proof.context -> string -> typ -> Proof.context * binder
  (*returns free variable corresponding to the given binder*)
  val binder_free : binder list -> int -> term
  (*replaces all binders by their corresponding free variable in the given term*)
  val replace_binders : binder list -> term -> term

  (* normalisations *)
  type type_normaliser = Type.tyenv -> typ -> typ
  val norm_type_match : type_normaliser
  val norm_type_unif : type_normaliser

  type term_normaliser = Envir.env -> term -> term
  val norm_term_match : term_normaliser
  val norm_term_unif : term_normaliser

  type term_type_normaliser = Type.tyenv -> term -> term
  type thm_normaliser = Proof.context -> Envir.env -> thm -> thm
  type thm_type_normaliser = thm_normaliser

  (*normalise types of a given variable and abstract*)
  val norm_abstract : term_type_normaliser -> Proof.context -> string -> term ->
    Envir.env -> thm -> thm
  val norm_abstract_env_thmq : term_type_normaliser -> Proof.context -> string ->
    term -> (Envir.env * thm) Seq.seq -> (Envir.env * thm) Seq.seq

  val norm_thm_types : type_normaliser -> thm_normaliser
  val norm_thm : type_normaliser -> term_normaliser -> thm_normaliser

  (* type unification *)

  (*raises Unification_Base.UNIF on failure*)
  val unify_types : Unification_Base.type_unifier
  (*raises Unification_Base.UNIF on failure*)
  val match_types : Unification_Base.type_matcher

  (* shared standard cases for unifiers *)
  val rigid_rigid : term_type_normaliser -> Unification_Base.type_unifier -> Proof.context -> term ->
    (string * typ) -> Envir.env -> (Envir.env * thm) Seq.seq
  val bound_bound : Proof.context -> int -> int -> binder list -> thm Seq.seq
  val comb_comb : thm_type_normaliser -> Unification_Base.unifier -> Proof.context ->
    (term * term) -> (term * term) -> Envir.env -> (Envir.env * thm) Seq.seq
  val args_args : thm_type_normaliser -> Unification_Base.unifier -> Proof.context ->
    (Envir.env * thm) Seq.seq -> term list -> term list -> (Envir.env * thm) Seq.seq

  (* logging *)
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

(* normalisations *)
type type_normaliser = Type.tyenv -> typ -> typ
type term_normaliser = Envir.env -> term -> term
type term_type_normaliser = Type.tyenv -> term -> term
type thm_normaliser = Proof.context -> Envir.env -> thm -> thm
type thm_type_normaliser = thm_normaliser

(** matching **)
val norm_type_match = Envir.subst_type
val norm_type_unif = Envir.norm_type

fun norm_term_match_same (Envir.Envir {tenv, tyenv, ...}) : term Same.operation =
  let
    val normT = Envir.subst_type_same tyenv
    fun norm (Const (a, T)) = Const (a, normT T)
      | norm (Free (a, T)) = Free (a, normT T)
      | norm (v as Var (xi, T)) =
          let
            fun lookup (Var (xi, T)) = (case Envir.lookup1 tenv (xi, T) of
                SOME u => u
              | NONE => raise Same.SAME)
          in
            (normT T |> (fn T => Same.commit lookup (Var (xi, T))))
            handle Same.SAME => lookup v
          end
      | norm (Abs (a, T, body)) = (Abs (a, normT T, Same.commit norm body)
          handle Same.SAME => Abs (a, T, norm body))
      | norm (Abs (_, _, body) $ t) = Same.commit norm (subst_bound (t, body))
      | norm (f $ t) =
          ((case norm f of
             Abs (_, _, body) => Same.commit norm (subst_bound (t, body))
           | nf => nf $ Same.commit norm t)
          handle Same.SAME => f $ norm t)
      | norm _ = raise Same.SAME
  in norm end

fun norm_term_match env = Same.commit (norm_term_match_same env)
val norm_term_unif = Envir.norm_term


(** theorems **)
fun norm_abstract norm_term_type ctxt name bvar (Envir.Envir {tyenv,...}) thm =
  let val bvar' = norm_term_type tyenv bvar
  in Unification_Base.abstract_rule name (Thm.cterm_of ctxt bvar') thm end

fun norm_abstract_env_thmq norm_term_type ctxt name bvar =
  Seq.map (fn (env, thm) => (env, norm_abstract norm_term_type ctxt name bvar env thm))

(*collect and normalise TVars of a term*)
fun collect_norm_types norm_type ctxt tyenv t =
  let
    val norm_type' = norm_type tyenv
    fun prep_type_entry x = (x, Thm.ctyp_of ctxt (norm_type' (TVar x)))
  in
    fold_types (fold_atyps (fn (TVar v) => TVars.add (prep_type_entry v) | _ => I)) t
    |> TVars.build
  end

(*collect and normalise Vars of a term*)
fun collect_norm_terms norm_type norm_term ctxt (env as Envir.Envir {tyenv,...}) t =
  let
    val norm_type' = norm_type tyenv
    val norm_term' = norm_term env
    fun prep_term_entry (x as (n, T)) = ((n, norm_type' T), Thm.cterm_of ctxt (norm_term' (Var x)))
  in
    fold_aterms (fn (Var v) => Vars.add (prep_term_entry v) | _ => I) t
    |> Vars.build
  end

(*normalise types of a theorem*)
fun norm_thm_types norm_types ctxt (Envir.Envir {tyenv, ...}) thm =
  let
    val prop = Thm.prop_of thm
    val type_inst = collect_norm_types norm_types ctxt tyenv prop
    val inst = (type_inst, Vars.empty)
  in Thm.instantiate inst thm end

(*normalise a theorem*)
fun norm_thm norm_types norm_terms ctxt (env as Envir.Envir {tyenv,...}) thm =
  let
    val prop = Thm.prop_of thm
    val type_inst = collect_norm_types norm_types ctxt tyenv prop
    val term_inst = collect_norm_terms norm_types norm_terms ctxt env prop
    val inst = (type_inst, term_inst)
  in Thm.instantiate inst thm end

(* type unification *)

fun match_types ctxt (T, U) (env as Envir.Envir {maxidx, tenv, tyenv}) =
  (if pointer_eq (T, U) then env
  else
    let val tyenv' = Sign.typ_match (Proof_Context.theory_of ctxt) (T, U) tyenv
    in Envir.Envir {maxidx = maxidx, tenv = tenv, tyenv = tyenv'} end)
  handle Type.TYPE_MATCH =>
    (@{log Logger.DEBUG} ctxt
      (fn _ => Pretty.block [
          Pretty.str "Failed to match types ",
          pretty_types ctxt [norm_type_match tyenv T, U]
        ] |> Pretty.string_of);
    raise Unification_Base.UNIF)

fun unify_types ctxt (T, U) (env as Envir.Envir {maxidx, tenv, tyenv}) =
  (if pointer_eq (T, U) then env
  else
    let val (tyenv', maxidx') =
      Sign.typ_unify (Proof_Context.theory_of ctxt) (T, U) (tyenv, maxidx)
    in Envir.Envir {maxidx = maxidx', tenv = tenv, tyenv = tyenv'} end)
  handle Type.TUNIFY =>
    (@{log Logger.DEBUG} ctxt
      (fn _ => Pretty.block [
          Pretty.str "Failed to unify types ",
          pretty_types ctxt (map (norm_type_unif tyenv) [T, U])
        ] |> Pretty.string_of);
    raise Unification_Base.UNIF)

(* shared standard cases for unifiers *)

fun rigid_rigid norm_term_type unify_types ctxt s (nt, Tt) env =
  let val (ns, Ts) = (if is_Const s then dest_Const else dest_Free) s
  in
    (if ns = nt then
      let val (env' as Envir.Envir {tyenv,...}) = unify_types ctxt (Ts, Tt) env
      in
        (env', Unification_Base.reflexive_term ctxt (norm_term_type tyenv s))
        |> Seq.single
      end
    else Seq.empty)
    handle Unification_Base.UNIF => Seq.empty
  end

fun bound_bound ctxt i j binders =
  if i = j then Seq.single (binder_free binders i |> Unification_Base.reflexive_term ctxt)
  else Seq.empty

fun comb_comb norm_thm_types unif ctxt (f, x) (g, y) env =
  let
    val unif' = unif ctxt
    val env_thmq = unif' (f, g) env
      |> Seq.maps (fn (env, thm_fg) => unif' (x, y) env |> Seq.map (apsnd (pair thm_fg)))
    fun combine (env, thmp) =
      (*normalise types for the combination theorem to succeed*)
      apply2 (norm_thm_types ctxt env) thmp
      |> uncurry Unification_Base.combination
      |> pair env
  in Seq.map combine env_thmq end

fun args_args norm_thm_types unif ctxt env_thmhq ss ts =
  (let
    val args = ss ~~ ts
    fun unif_arg tp = Seq.maps
      (fn (env, thms) => unif ctxt tp env |> Seq.map (apsnd (fn thm => thm :: thms)))
    fun unif_args env = fold unif_arg args (Seq.single (env, []))
    (*combine the theorems*)
    fun combine thmh (env_res, arg_thms) =
      let
        (*normalise types for the combination theorem to succeed*)
        val norm_thm_types' = norm_thm_types ctxt env_res
        fun norm_combine thm_arg thm = norm_thm_types' thm_arg |> Unification_Base.combination thm
      in (env_res, fold_rev norm_combine arg_thms (norm_thm_types' thmh)) end
  in Seq.maps (fn (env, thmh) => unif_args env |> Seq.map (combine thmh)) env_thmhq end)
  handle ListPair.UnequalLengths => Seq.empty


(* logging *)

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

