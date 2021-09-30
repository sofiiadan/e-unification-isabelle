(*  Title:      Pure/pattern.ML
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

  val e_unify : Unification_Base.unifier -> Unification_Base.unifier
  val unify : Unification_Base.unifier
  val unify_hints : Unification_Base.unifier
end

structure Higher_Order_Pattern_Unification : HIGHER_ORDER_PATTERN_UNIFICATION =
struct

structure Logger = @{new_logger "higher_order_pattern_unification"}

structure Util = Unification_Util

fun string_of_term ctxt env binders t =
  (map (Free o fst) binders, t)
  |> subst_bounds
  |> Envir.norm_term env
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

fun idx [] _ = raise Unification_Base.UNIF
  | idx (i :: is) j = if i = j then length is else idx is j

fun mkabs (binders, is, t) =
  let fun abstract i acc = let val ((x, T), _) = nth binders i
    in Abs (x, T, acc) end
  in fold_rev abstract is t end

fun ints_of bs =
  (*collects arguments and checks if they are all distinct, bound variables*)
  let fun dest_check (Bound i) acc =
            if member (op =) acc i then raise Unification_Base.PATTERN else i :: acc
        | dest_check _ _ = raise Unification_Base.PATTERN
  in fold_rev dest_check bs [] end

fun ints_of' env ts = ints_of (map (Envir.head_norm env) ts)

fun app (s, []) = s
  | app (s, (i :: is)) = app (s $ Bound i, is)

(*split_type ([T1,....,Tn]---> T) n = ([Tn,...,T1], T)*)
fun split_type t n =
  let fun split (T, 0, Ts) = (Ts, T)
        | split (Type ("fun", [T1, T2]), n, Ts) = split (T2, n - 1, T1 :: Ts)
        | split _ = raise Fail "split_type"
  in split (t, n, []) end

fun type_of_G (Envir.Envir {tyenv,...}) (T, n, is) =
  let val (Ts, U) = split_type (Envir.norm_type tyenv T) n
  in map (nth Ts) is ---> U end

fun mk_hnf (binders, is, G, js) = mkabs (binders, is, app (G, js))

fun mk_new_hnf (env, binders, is, F as (a, _), T, js) =
  let val (env', G) = Envir.genvar a (env, type_of_G env (T, length is, js))
  in Envir.update ((F, T), mk_hnf (binders, is, G, js)) env' end

(*predicate: downto0 (is, n) <=> is = [n, n - 1, ..., 0]*)
fun downto0 ([], n) = n = ~1
  | downto0 (i :: is, n) = i = n andalso downto0 (is, n - 1)

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
  let val norm_type = Envir.norm_type tyenv
  in list_comb (Var (n, norm_type T), map (map_types norm_type o Util.binder_free binders) is) end

fun seq_try sq = Unification_Util.seq_try Unification_Base.UNIF sq

fun flexflex1 ctxt (env, binders, F, Fty, Fty', is, js) =
  let
    val env' = Util.unify_types ctxt (Fty, Fty') env
    val thm = app_free env binders F Fty is |> Unification_Base.reflexive_term ctxt
  in
    if is = js then (env', thm)
    else
      let
        val ks = mk_ff_list (is, js)
        val env'' = mk_new_hnf (env', binders, is, F, Fty, ks)
      in (env'', thm) end
  end

fun flexflex2 ctxt (env, binders, F, Fty, is, G, Gty, js) =
  let
    val var_app = app_free env binders F Fty is
    val binder_types = map (snd o fst) binders
    val env' = Util.unify_types ctxt
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

fun flexrigid ctxt (params as (env, binders, F, Fty, is, t)) =
  if occurs (F, t, env) then (ocheck_fail ctxt (F, t, binders, env); raise Unification_Base.UNIF)
  else
    let
      val var_app = app_free env binders F Fty is
      val binder_types = map (snd o fst) binders
      val env' = Util.unify_types ctxt
        (fastype_of1 (binder_types, var_app), Envir.fastype env binder_types t) env
      val (u, env'') = proj ctxt (t, env', binders, is)
      val env''' = Envir.update ((F, Fty), mkabs (binders, is, u)) env''
      val thm = Unification_Base.reflexive_term ctxt var_app
    in (env''', thm) end
    handle (exn as Unification_Base.UNIF) => (proj_fail ctxt params; raise exn)

fun unif unif_theory ctxt binders tp env =
  let val tp' = apply2 (Envir.head_norm env) tp
  in
    (case tp' of
      (*eta-expand on the fly*)
        (Abs (ns, Ts, ts), Abs (nt, Tt, tt)) =>
          let
            val env' = Util.unify_types ctxt (Ts, Tt) env
            val name = if ns = "" then nt else ns
            val (ctxt', binder as (_, bvar)) = Util.new_binder ctxt name Ts
            val env_thmq = unif unif_theory ctxt' (binder :: binders) (ts, tt) env' |> seq_try
          in Seq.map (Util.abstract ctxt' name bvar) env_thmq end
      | (Abs (ns, Ts, ts), t) =>
          let
            val (ctxt', binder as (_, bvar)) = Util.new_binder ctxt ns Ts
            val env_thmq =
              unif unif_theory ctxt' (binder :: binders) (ts, incr_boundvars 1 t $ Bound 0) env
              |> seq_try
          in Seq.map (Util.abstract ctxt' ns bvar) env_thmq end
      | (s, t as Abs _) =>
          unif unif_theory ctxt binders (t, s) env |> Seq.map (apsnd Unification_Base.symmetric)
      (*case distinctions on head term*)
      | (s, t) => (case (strip_comb s, strip_comb t) of
          ((Var (F, Fty), ss), (Var (G, Gty), ts)) =>
            (if F = G then
              flexflex1 ctxt (env, binders, F, Fty, Gty, ints_of' env ss, ints_of' env ts)
            else flexflex2 ctxt (env, binders, F, Fty, ints_of' env ss, G, Gty, ints_of' env ts))
            |> Seq.single
        | ((Var (F, Fty), ss), _) =>
            flexrigid ctxt (env, binders, F, Fty, ints_of' env ss, t) |> Seq.single
        | (_, (Var (F, Fty), ts)) =>
            flexrigid ctxt (env, binders, F, Fty, ints_of' env ts, s) |> Seq.single
        | ((Const c, ss), (Const d, ts)) =>
            rigidrigid unif_theory ctxt (env, binders, Const c, d, ss, ts) |> seq_try
        | ((Free f, ss), (Free g, ts))   =>
            rigidrigid unif_theory ctxt (env, binders, Free f, g, ss, ts) |> seq_try
        | ((Bound i, ss), (Bound j, ts)) =>
            rigidrigidB unif_theory ctxt (env, binders, i, j, ss, ts) |> seq_try
        | _ => raise Unification_Base.UNIF))
    handle Unification_Base.UNIF =>
      let
        (*replace all Bounds by Frees to make fallback unification possible*)
        val (s', t') = apply2 (Unification_Util.replace_binders binders) tp'
        val _ = @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
            Pretty.str "Failed to pattern unify; calling theory unifier for ",
            Util.pretty_terms ctxt [s', t']
          ]
          |> Pretty.string_of)
      in unif_theory ctxt (s', t') env end
  end

and unif_args unif_theory ctxt binders ss ts env thm =
  let
    fun unif_arg tp = Seq.maps
      (fn (env, thms) => unif unif_theory ctxt binders tp env
        |> Seq.map (apsnd (fn thm => thm :: thms)))
    val args = ss ~~ ts handle ListPair.UnequalLengths => raise Unification_Base.UNIF
    val env_arg_thmsq = fold unif_arg args (Seq.single (env, []))
    (*combine the theorems*)
    fun combine (env_res, arg_thms) =
      let
        val norm_thm_types = Util.norm_thm_types ctxt env_res
        fun norm_combine thm_arg thm = norm_thm_types thm_arg |> Unification_Base.combination thm
      in (env_res, fold_rev norm_combine arg_thms (norm_thm_types thm)) end
  in Seq.map combine env_arg_thmsq end

and rigidrigid unif_theory ctxt (env, binders, t, (b, Tb), ss, ts) =
  let val (a, Ta) = (if is_Const t then dest_Const else dest_Free) t
  in
    if a <> b then Seq.empty
    else
      let
        val env' = Util.unify_types ctxt (Ta, Tb) env
        val thm = Unification_Base.reflexive_term ctxt t
      in unif_args unif_theory ctxt binders ss ts env' thm end
  end

and rigidrigidB unif_theory ctxt (env, binders, i, j, ss, ts) =
  if i <> j then Seq.empty
  else
    let val thm = Util.binder_free binders i |> Unification_Base.reflexive_term ctxt
    in unif_args unif_theory ctxt binders ss ts env thm end

(*higher-order pattern e-unification*)
fun e_unify unif_theory ctxt (s, t) env =
  (@{log Logger.DEBUG} ctxt (fn _ =>
    Pretty.block [
      Pretty.str "Higher-order pattern unifying ",
      Util.pretty_terms ctxt (map (Envir.norm_term env) [s, t])
    ]
    |> Pretty.string_of);
  unif unif_theory ctxt [] (s, t) env)

(*standard higher-order pattern unification*)
val unify = e_unify (K o K o K Seq.empty)

(*higher-order pattern unification with hints from context*)
fun unify_hints ctxt =
  let
    val hints = Unification_Hints.gen_hint_list ctxt
    fun unify ctxt = e_unify (Unification_Hints.try_hints Pattern.match unify hints) ctxt
  in unify ctxt end

end
