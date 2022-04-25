(*  Title:      E_Unification/higher_order_pattern_unification.ML
    Author:     Tobias Nipkow, Christine Heinzelmann, Stefan Berghofer, and
                Kevin Kappelmann TU Muenchen

E-Unification of Higher-Order Patterns.

See also:
Tobias Nipkow. Functional Unification of Higher-Order Patterns.
In Proceedings of the 8th IEEE Symposium Logic in Computer Science, 1993.

TODO: optimize red by special-casing it
*)
signature HIGHER_ORDER_PATTERN_UNIFICATION =
sig
  structure Logger : LOGGER

  val e_match : Unification_Base.type_unifier -> Unification_Base.matcher ->
    Unification_Base.unifier
  val match : Unification_Base.unifier
  val match_hints : Unification_Base.unifier

  val e_unify : Unification_Base.type_unifier -> Unification_Base.unifier ->
    Unification_Base.unifier
  val unify : Unification_Base.unifier
  val unify_hints : Unification_Base.unifier

end

structure Higher_Order_Pattern_Unification : HIGHER_ORDER_PATTERN_UNIFICATION =
struct

(* shared utils *)

structure Logger = @{new_logger "higher_order_pattern_unification"}

structure Util = Unification_Util

fun seq_try sq = Util.seq_try Unification_Base.UNIF sq

(*predicate: downto0 (is, n) <=> is = [n, n - 1, ..., 0]*)
fun downto0 ([], n) = n = ~1
  | downto0 (i :: is, n) = i = n andalso downto0 (is, n - 1)

fun mkabs (binders, is, t) =
  let fun abstract i acc =
    let val ((x, T), _) = nth binders i
    in Abs (x, T, acc) end
  in fold_rev abstract is t end

fun idx [] _ = raise Unification_Base.UNIF
  | idx (i :: is) j = if i = j then length is else idx is j

fun ints_of bs =
  (*collects arguments and checks if they are all distinct, bound variables*)
  let fun dest_check (Bound i) acc =
          if member (op =) acc i then raise Unification_Base.PATTERN else i :: acc
        | dest_check _ _ = raise Unification_Base.PATTERN
  in fold_rev dest_check bs [] end

fun app (s, []) = s
  | app (s, (i :: is)) = app (s $ Bound i, is)

(* matching *)

fun mapbnd f =
  let fun mpb d (Bound i) = if i < d then Bound i else Bound (f (i - d) + d)
        | mpb d (Abs (s, T, t)) = Abs (s, T, mpb (d + 1) t)
        | mpb d (u1 $ u2) = (mpb d u1) $ (mpb d u2)
        | mpb _ atom = atom
  in mpb 0 end

fun red (Abs (_, _, s)) (i :: is) js = red s is (i :: js)
  | red t [] [] = t
  | red t is jn = app (mapbnd (nth jn) t, is)

fun match_bind (tenv, binders, ixn, T, is, t) =
  let val js = loose_bnos t
  in
    if null is then
      if null js then Vartab.update_new (ixn, (T, t)) tenv
      else raise Unification_Base.UNIF
    else if subset (op =) (js, is) then
      let val t' = if downto0 (is, length binders - 1) then t else mapbnd (idx is) t
      in Vartab.update_new (ixn, (T, mkabs (binders, is, t'))) tenv end
    else raise Unification_Base.UNIF
  end

(** higher-order pattern E-unification **)
fun e_match match_types match_theory ctxt (pt as (p, t)) env =
  let
    (*calls match_theory on failure;
    generated theorem is already normalised wrt. the resulting environment*)
    fun match binders ctxt (p, t) (env as Envir.Envir {maxidx, tenv, tyenv}) =
      (case (p, t) of
        (Abs (np, Tp, tp), Abs (nt, Tt, tt)) =>
          let
            val env' = match_types ctxt (Tp, Tt) env
            val name = if np = "" then nt else np
            val (ctxt', binder as (_, bvar)) = Util.new_binder ctxt name Tt
          in
            match (binder :: binders) ctxt' (tp, tt) env'
            |> seq_try
            (*Note: types of binders are already fixed to the object's binder's type
            ==> we pass the identity type normaliser*)
            |> Util.norm_abstract_env_thmq (K I) ctxt' name bvar
          end
      (*eta-expand on the fly*)
      | (Abs (np, Tp, tp), _) =>
          let
            val Tt = Envir.subst_type tyenv Tp
            val (ctxt', binder as (_, bvar)) = Util.new_binder ctxt np Tt
          in
            match (binder :: binders) ctxt' (tp, incr_boundvars 1 t $ Bound 0) env
            |> seq_try
            |> Util.norm_abstract_env_thmq (K I) ctxt' np bvar
          end
      | (_, Abs (nt, Tt, tt)) =>
          let val (ctxt', binder as (_, bvar)) = Util.new_binder ctxt nt Tt
          in
            match (binder :: binders) ctxt' (incr_boundvars 1 p $ Bound 0, tt) env
            |> seq_try
            |> Util.norm_abstract_env_thmq (K I) ctxt' nt bvar
          end
      | (Bound i, Bound j) => Util.bound_bound ctxt i j binders |> seq_try |> Seq.map (pair env)
      | (Free _, Free g) =>
          (*normalise the types in rigid-rigid cases*)
          Util.rigid_rigid (map_types o Util.norm_type_match) match_types ctxt p g env
          |> seq_try
      | (Const _, Const d) =>
          Util.rigid_rigid (map_types o Util.norm_type_match) match_types ctxt p d env
          |> seq_try
      | _ => case strip_comb p of
          (Var (x, T), ps) =>
            let
              val is = ints_of ps
              val T' = Util.norm_type_match tyenv T
            in
              case Envir.lookup1 tenv (x, T') of
                NONE =>
                  let
                    val tenv' = match_bind (tenv, binders, x, T', is, t)
                    val env' = Envir.Envir {maxidx=maxidx, tenv=tenv', tyenv=tyenv}
                    val t' = Util.replace_binders binders t
                  in Seq.single (env', Unification_Base.reflexive_term ctxt t') end
              | SOME ph' =>
                  if Envir.aeconv (t, red ph' is []) then
                    Seq.single (env, Unification_Base.reflexive_term ctxt
                      (Util.replace_binders binders t))
                  else raise Unification_Base.UNIF
            end
        | (ph, ps) =>
            let val (th, ts) = strip_comb t
            in
              case (ph, th) of
                (Abs _, _) => raise Unification_Base.PATTERN
              | (_, Abs _) => raise Unification_Base.PATTERN
              | _ =>
                  if null ps orelse null ts then raise Unification_Base.UNIF
                  else
                    let val env_thmhq = match binders ctxt (ph, th) env
                    in
                      (*Note: types of theorems are already normalised ==> we pass
                      the identity type normaliser*)
                      Util.args_args (K o K I) (match binders) ctxt env_thmhq ps ts
                      |> seq_try
                    end
            end)
      handle Unification_Base.UNIF =>
        let
          (*replace all Bounds by Frees so that the theory matcher receives a closed term*)
          val (p', t') = apply2 (Util.replace_binders binders) (p, t)
            |> apfst (Util.norm_term_match env)
          val _ = @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
              Pretty.str "Failed to pattern match; calling theory matcher for ",
              Util.pretty_unif ctxt (p', t')
            ]
            |> Pretty.string_of)
        in match_theory ctxt (p', t') env end

  in
    (@{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.block [
        Pretty.str "Higher-order pattern matching ",
        Util.pretty_unif ctxt (Util.norm_term_match env p, t)
      ]
      |> Pretty.string_of);
    match [] ctxt pt env)
  end


(*standard higher-order pattern matching*)
val match = e_match Util.match_types (K o K o K Seq.empty)

(*higher-order pattern matching with hints from context*)
fun match_hints ctxt =
  let
    val ctxt' = Config.put Unification_Hints.try_symmetric false ctxt
    val hints = Unification_Hints.gen_hint_list ctxt
    val norm_thm_match = Util.norm_thm Util.norm_type_match Util.norm_term_match
    (*generated theorems are already in normal form ==> no normalisation needed*)
    val norm_thm_unif = K o K I
    fun matcher ctxt = e_match Util.match_types
      (Unification_Hints.try_hints norm_thm_match match norm_thm_unif matcher hints)
      ctxt
  in matcher ctxt' end


(*unification*)

fun string_of_term ctxt env binders t =
  (map (Free o fst) binders, t)
  |> subst_bounds
  |> Util.norm_term_unif env
  |> Syntax.string_of_term ctxt

fun bname binders = fst o fst o nth binders
fun bnames binders is = map (bname binders) is |> space_implode " "

fun proj_fail ctxt (env, binders, F, _, is, t) =
  @{log Logger.DEBUG} ctxt (fn _ =>
    let
      val f = Term.string_of_vname F
      val xs = bnames binders is
      val u = string_of_term ctxt env binders t
      val ys = bnames binders (subtract (op =) is (loose_bnos t))
    in
      cat_lines [
        "Cannot unify variable " ^ f ^ " (depending on bound variables " ^ xs ^ ")",
        "with term " ^ u,
        "Term contains additional bound variable(s) " ^ ys
      ]
    end)

fun ocheck_fail ctxt (F, t, binders, env) =
  @{log Logger.DEBUG} ctxt (fn _ => cat_lines [
      "Variable " ^ Term.string_of_vname F ^ " occurs in term",
      string_of_term ctxt env binders t,
      "Cannot unify!"
    ])

fun occurs (F, t, env) =
  let fun occ (Var (G, T)) = (case Envir.lookup env (G, T) of
            SOME t => occ t
          | NONE => F = G)
        | occ (t1 $ t2) = occ t1 orelse occ t2
        | occ (Abs (_, _, t)) = occ t
        | occ _ = false
  in occ t end

fun ints_of' env ts = ints_of (map (Envir.head_norm env) ts)

(*split_type ([T1,....,Tn]---> T) n = ([Tn,...,T1], T)*)
fun split_type t n =
  let fun split (T, 0, Ts) = (Ts, T)
        | split (Type ("fun", [T1, T2]), n, Ts) = split (T2, n - 1, T1 :: Ts)
        | split _ = raise Fail "split_type"
  in split (t, n, []) end

fun type_of_G (Envir.Envir {tyenv,...}) (T, n, is) =
  let val (Ts, U) = split_type (Util.norm_type_unif tyenv T) n
  in map (nth Ts) is ---> U end

fun mk_hnf (binders, is, G, js) = mkabs (binders, is, app (G, js))

fun mk_new_hnf (env, binders, is, F as (a, _), T, js) =
  let val (env', G) = Envir.genvar a (env, type_of_G env (T, length is, js))
  in Envir.update ((F, T), mk_hnf (binders, is, G, js)) env' end

(*mk_proj_list is = [ |is| - k - 1 | 0 <= k < |is| and is[k] >= 0 ]*)
fun mk_proj_list is =
  let fun mk (SOME _) (acc, j) = (j :: acc, j + 1)
        | mk NONE (acc, j) = (acc, j + 1)
  in fold_rev mk is ([], 0) |> fst end

fun proj ctxt (s, env, binders, is) =
  let
    fun trans d i = if i < d then i else idx is (i - d) + d
    fun pr (s, env, d, binders) = (case Envir.head_norm env s of
        Abs (a, T, t) =>
          let
            val (_, binder) = Util.new_binder ctxt a T
            val (t', env'') = pr (t, env, d + 1, binder :: binders)
          in (Abs (a, T, t'), env'') end
      | t => (case strip_comb t of
          (c as Const _, ts) =>
            let val (ts', env') = prs (ts, env, d, binders)
            in (list_comb (c, ts'), env') end
        | (f as Free _, ts) =>
            let val (ts', env') = prs (ts, env, d, binders)
            in (list_comb (f, ts'), env') end
        | (Bound i, ts) =>
            let
              val j = trans d i
              val (ts', env') = prs (ts, env, d, binders)
            in (list_comb (Bound j, ts'), env') end
        | (Var (F as (a, _), Fty), ts) =>
            let
              val js = ints_of' env ts
              val js' = map (try (trans d)) js
              val ks = mk_proj_list js'
              val ls = map_filter I js'
              val Hty = type_of_G env (Fty, length js, ks)
              val (env', H) = Envir.genvar a (env, Hty)
              val env'' = Envir.update ((F, Fty), mk_hnf (binders, js, H, ks)) env'
            in (app (H, ls), env'') end
        | _  => raise Unification_Base.PATTERN))
    and prs (s :: ss, env, d, binders) =
          let
            val (s', env1) = pr (s, env, d, binders)
            val (ss', env2) = prs (ss, env1, d, binders)
          in (s' :: ss', env2) end
      | prs ([], env, _, _) = ([], env)
  in
    if downto0 (is, length binders - 1) then (s, env)
    else pr (s, env, 0, binders)
  end

(*mk_ff_list (is, js) = [ |is| - k - 1 | 0 <= k < |is| and is[k] = js[k] ]*)
fun mk_ff_list (is,js) =
    let fun mk ([], [], _) = []
          | mk (i :: is, j :: js, k) =
              if i = j then k :: mk (is, js, k - 1)
              else mk (is, js, k - 1)
          | mk _ = raise Fail "mk_ff_list"
    in mk (is, js, length is - 1) end;

fun app_free (Envir.Envir {tyenv,...}) binders n T is =
  let val norm_type = Util.norm_type_unif tyenv
  in list_comb (Var (n, norm_type T), map (map_types norm_type o Util.binder_free binders) is) end

fun flexflex1 unify_types ctxt (env, binders, F, Fty, Fty', is, js) =
  let
    val env' = unify_types ctxt (Fty, Fty') env
    val thm = app_free env binders F Fty is |> Unification_Base.reflexive_term ctxt
  in
    if is = js then (env', thm)
    else
      let
        val ks = mk_ff_list (is, js)
        val env'' = mk_new_hnf (env', binders, is, F, Fty, ks)
      in (env'', thm) end
  end

fun flexflex2 unify_types ctxt (env, binders, F, Fty, is, G, Gty, js) =
  let
    val var_app = app_free env binders F Fty is
    val binder_types = map (snd o fst) binders
    val env' = unify_types ctxt
      (fastype_of1 (binder_types, var_app), Envir.fastype env binder_types (app (Var (G, Gty), js)))
      env
    val thm = Unification_Base.reflexive_term ctxt var_app
    fun ff (F, Fty, is, G as (a, _), Gty, js) =
      if subset (op =) (js, is) then
        let
          val t = mkabs (binders, is, app (Var (G, Gty), map (idx is) js))
          val env'' = Envir.update ((F, Fty), t) env'
        in (env'', thm) end
      else
        let
          val ks = inter (op =) js is
          val Hty = type_of_G env' (Fty, length is, map (idx is) ks)
          val (env'', H) = Envir.genvar a (env', Hty)
          fun lam is = mkabs (binders, is, app (H, map (idx is) ks))
          val env''' =
            Envir.update ((F, Fty), lam is) env''
            |> Envir.update ((G, Gty), lam js)
        in (env''', thm) end
  in
    if is_less (Term_Ord.indexname_ord (G, F)) then ff (F, Fty, is, G, Gty, js)
    else ff (G, Gty, js, F, Fty, is)
  end

fun flexrigid unify_types ctxt (params as (env, binders, F, Fty, is, t)) =
  if occurs (F, t, env) then (ocheck_fail ctxt (F, t, binders, env); raise Unification_Base.UNIF)
  else
    ((let
      val var_app = app_free env binders F Fty is
      val binder_types = map (snd o fst) binders
      val env' = unify_types ctxt
        (fastype_of1 (binder_types, var_app), Envir.fastype env binder_types t) env
      val (u, env'') = proj ctxt (t, env', binders, is)
      val env''' = Envir.update ((F, Fty), mkabs (binders, is, u)) env''
      val thm = Unification_Base.reflexive_term ctxt var_app
    in (env''', thm) end)
    handle (exn as Unification_Base.UNIF) => (proj_fail ctxt params; raise exn))

(** higher-order pattern E-unification **)
fun e_unify unify_types unify_theory ctxt (tp as (s, t)) env =
  let
    (*calls unify_theory on failure*)
    fun unif binders ctxt tp env =
      let val (tp' as (s', t')) = apply2 (Envir.head_norm env) tp
      in
        (case tp' of
          (Abs (ns, Ts, ts), Abs (nt, Tt, tt)) =>
            let
              val env' = unify_types ctxt (Ts, Tt) env
              val name = if ns = "" then nt else ns
              val (ctxt', binder as (_, bvar)) = Util.new_binder ctxt name Ts
            in
              unif (binder :: binders) ctxt' (ts, tt) env'
              |> seq_try
              |> Util.norm_abstract_env_thmq (map_types o Util.norm_type_unif) ctxt' name bvar
            end
        (*eta-expand on the fly*)
        | (Abs (ns, Ts, ts), _) =>
            let val (ctxt', binder as (_, bvar)) = Util.new_binder ctxt ns Ts
            in
              unif (binder :: binders) ctxt' (ts, incr_boundvars 1 t' $ Bound 0) env
              |> seq_try
              |> Util.norm_abstract_env_thmq (map_types o Util.norm_type_unif) ctxt' ns bvar
            end
        | (_, Abs _) => unif binders ctxt (t', s') env |> Seq.map (apsnd Unification_Base.symmetric)
        | (Bound i, Bound j) => Util.bound_bound ctxt i j binders |> seq_try |> Seq.map (pair env)
        (*we do not normalise types in base cases*)
        | (Free _, Free g) => Util.rigid_rigid (K I) unify_types ctxt s' g env |> seq_try
        | (Const _, Const d) => Util.rigid_rigid (K I) unify_types ctxt s' d env |> seq_try
        (*case distinctions on head term*)
        | _ => case (strip_comb s', strip_comb t') of
            ((Var (F, Fty), ss), (Var (G, Gty), ts)) =>
              (if F = G then
                flexflex1 unify_types ctxt (env, binders, F, Fty, Gty, ints_of' env ss, ints_of' env ts)
              else
                flexflex2 unify_types ctxt (env, binders, F, Fty, ints_of' env ss, G, Gty, ints_of' env ts))
              |> Seq.single
          | ((Var (F, Fty), ss), _) =>
              flexrigid unify_types ctxt (env, binders, F, Fty, ints_of' env ss, t')|> Seq.single
          | (_, (Var (F, Fty), ts)) =>
              flexrigid unify_types ctxt (env, binders, F, Fty, ints_of' env ts, s') |> Seq.single
          | ((sh, ss), (th, ts)) =>
              if null ss orelse null ts then raise Unification_Base.UNIF
              else
                let val env_thmhq = unif binders ctxt (sh, th) env
                in
                  (*but we have to normalise in comb cases*)
                  Util.args_args (Util.norm_thm_types Util.norm_type_unif) (unif binders) ctxt
                    env_thmhq ss ts
                  |> seq_try
                end)
        handle Unification_Base.UNIF =>
          let
            (*replace all Bounds by Frees so that the theory unifier receives a closed term*)
            val (s', t') = apply2 (Util.norm_term_unif env o Util.replace_binders binders) tp'
            val _ = @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
                Pretty.str "Failed to pattern unify; calling theory unifier for ",
                Util.pretty_unif ctxt (s', t')
              ]
              |> Pretty.string_of)
          in unify_theory ctxt (s', t') env end
      end
  in
    (@{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.block [
        Pretty.str "Higher-order pattern unifying ",
        Util.pretty_unif ctxt (apply2 (Envir.norm_term env) (s, t))
      ]
      |> Pretty.string_of);
    unif [] ctxt tp env)
  end

(*standard higher-order pattern unification*)
val unify = e_unify Util.unify_types (K o K o K Seq.empty)

(*higher-order pattern unification with hints from context*)
fun unify_hints ctxt =
  let
    val hints = Unification_Hints.gen_hint_list ctxt
    (*no normalisation after matching required since all results are normalised by norm_thm_unif*)
    val norm_thm_match = K o K I
    val norm_thm_unif = Util.norm_thm Util.norm_type_unif Util.norm_term_unif
    fun unify ctxt = e_unify Util.unify_types
      (Unification_Hints.try_hints norm_thm_match match norm_thm_unif unify hints) ctxt
  in unify ctxt end


end
