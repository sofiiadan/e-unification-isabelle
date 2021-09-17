(*  Title:      Pure/pattern.ML
    Author:     Tobias Nipkow, Christine Heinzelmann, Stefan Berghofer, and
                Kevin Kappelmann TU Muenchen

Unification of Higher-Order Patterns with unification hints.

See also:
Tobias Nipkow. Functional Unification of Higher-Order Patterns.
In Proceedings of the 8th IEEE Symposium Logic in Computer Science, 1993.

TODO: optimize red by special-casing it
*)
signature HIGHER_ORDER_PATTERN_UNIFICATION =
sig

  structure Logger : LOGGER
  val unify : Unification_Types.unifier
  val unify_hints : Unification_Types.unifier

end

structure Higher_Order_Pattern_Unification : HIGHER_ORDER_PATTERN_UNIFICATION =
struct

structure Logger = @{new_logger "higher_order_pattern_unification"}

structure Hints = Unification_Hints
structure Util = Unification_Util

fun string_of_term ctxt env binders t =
  (map (Free o fst) binders, t)
  |> subst_bounds
  |> Envir.norm_term env
  |> Syntax.string_of_term ctxt

fun bname binders = fst o fst o nth binders
fun bnames binders is = map (bname binders) is |> space_implode " "

fun clash context a b =
  @{log Logger.DEBUG} (Context.proof_of context) (fn () => "Clash: " ^ a ^ " =/= " ^ b)

fun boundVar binders i = "bound variable " ^ bname binders i ^ " (depth " ^ string_of_int i ^ ")"

fun clashBB context binders i j = clash context (boundVar binders i) (boundVar binders j)

fun clashB context binders i s = clash context (boundVar binders i) s

fun proj_fail context (env, binders, F, _, is, t) =
  let val ctxt = Context.proof_of context
  in
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
  end

fun ocheck_fail context (F, t, binders, env) =
  let val ctxt = Context.proof_of context
  in
    @{log Logger.DEBUG} ctxt (fn _ => cat_lines [
        "Variable " ^ Term.string_of_vname F ^ " occurs in term",
        string_of_term ctxt env binders t,
        "Cannot unify!"
      ])
  end

fun occurs (F, t, env) =
  let fun occ (Var (G, T)) = (case Envir.lookup env (G, T) of
            SOME t => occ t
          | NONE => F = G)
        | occ (t1 $ t2) = occ t1 orelse occ t2
        | occ (Abs (_, _, t)) = occ t
        | occ _ = false
  in occ t end

fun idx [] _ = raise Unification_Types.UNIF
  | idx (i :: is) j = if i = j then length is else idx is j

fun mkabs (binders, is, t) =
  let fun abstract i acc = let val ((x, T), _) = nth binders i
    in Abs (x, T, acc) end
  in fold_rev abstract is t end

fun ints_of bs =
  (*collects arguments and checks if they are all distinct, bound variables*)
  let fun dest_check (Bound i) acc =
            if member (op =) acc i then raise Unification_Types.PATTERN else i :: acc
        | dest_check _ _ = raise Unification_Types.PATTERN
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

fun proj context (s, env, binders, is) =
  let
    fun trans d i = if i < d then i else idx is (i - d) + d
    fun pr (s, env, d, binders) = (case Envir.head_norm env s of
          Abs (a, T, t) =>
            let
              val (_, binder) = Util.new_binder context a T
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
            | _  => raise Unification_Types.PATTERN))
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

fun flexflex1 context (env, binders, F, Fty, Fty', is, js) =
  let
    val env' = Util.unify_types context (Fty, Fty') env
    val thm = app_free env binders F Fty is
      |> Hints.reflexive_term context
  in
    if is = js then (env', thm)
    else
      let
        val ks = mk_ff_list (is, js)
        val env'' = mk_new_hnf (env', binders, is, F, Fty, ks)
      in (env'', thm) end
  end

fun flexflex2 context (env, binders, F, Fty, is, G, Gty, js) =
  let
    val var_app = app_free env binders F Fty is
    val binder_types = map (snd o fst) binders
    val env' = Util.unify_types context
      (fastype_of1 (binder_types, var_app), Envir.fastype env binder_types (app (Var (G, Gty), js)))
      env
    val thm = Hints.reflexive_term context var_app
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

fun unif try_hints_fun hints hints_unifier context binders (s, t) env =
  case (Envir.head_norm env s, Envir.head_norm env t) of
      (Abs (ns, Ts, ts), Abs (nt, Tt, tt)) =>
        let
          val env' = Util.unify_types context (Ts, Tt) env
          val name = if ns = "" then nt else ns
          val (context', binder as (_, bvar)) = Util.new_binder context name Ts
          val (env'', thm) =
            unif try_hints_fun hints hints_unifier context' (binder :: binders) (ts, tt) env'
          val bvar' = map_types (Envir.norm_type (Envir.type_env env'')) bvar
          val thm' = Hints.abstract_rule name (Thm.cterm_of (Context.proof_of context') bvar') thm
        in (env'', thm') end
    | (Abs (ns, Ts, ts), t) =>
        let
          val (context', binder as (_, bvar)) = Util.new_binder context ns Ts
          val (env', thm) =
            unif try_hints_fun hints hints_unifier context' (binder :: binders)
              (ts, incr_boundvars 1 t $ Bound 0) env
          val bvar' = map_types (Envir.norm_type (Envir.type_env env')) bvar
          val thm' = Hints.abstract_rule ns (Thm.cterm_of (Context.proof_of context') bvar') thm
        in (env', thm') end
    | (s, t as Abs _) =>
        unif try_hints_fun hints hints_unifier context binders (t, s) env
        ||> Hints.symmetric
    | p =>
        cases try_hints_fun hints hints_unifier context (binders, env, p)

and cases try_hints_fun hints hints_unifier context (binders, env, (s, t)) =
  (case (strip_comb s, strip_comb t) of
        ((Var (F, Fty), ss), (Var (G, Gty), ts)) =>
          if F = G then
            flexflex1 context (env, binders, F, Fty, Gty, ints_of' env ss, ints_of' env ts)
          else flexflex2 context (env, binders, F, Fty, ints_of' env ss, G, Gty, ints_of' env ts)
      | ((Var (F, Fty), ss), _) =>
          flexrigid context (env, binders, F, Fty, ints_of' env ss, t)
      | (_, (Var (F, Fty), ts)) =>
          flexrigid context (env, binders, F, Fty, ints_of' env ts, s)
      | ((Const c, ss), (Const d, ts)) =>
          rigidrigid try_hints_fun hints hints_unifier context (env, binders, Const c, d, ss, ts)
      | ((Free f, ss), (Free g, ts))   =>
          rigidrigid try_hints_fun hints hints_unifier context (env, binders, Free f, g, ss, ts)
      | ((Bound i, ss), (Bound j, ts)) =>
          rigidrigidB try_hints_fun hints hints_unifier context (env,binders, i, j, ss, ts)
      | ((Const (c, _), _), (Free (f,_), _)) =>
          (clash context c f; raise Unification_Types.UNIF)
      | ((Const (c, _), _), (Bound i, _))   =>
          (clashB context binders i c; raise Unification_Types.UNIF)
      | ((Free (f, _), _), (Const (c, _), _)) =>
          (clash context f c; raise Unification_Types.UNIF)
      | ((Free (f, _), _), (Bound i, _)) =>
          (clashB context binders i f; raise Unification_Types.UNIF)
      | ((Bound i, _), (Const (c, _), _)) =>
          (clashB context binders i c; raise Unification_Types.UNIF)
      | ((Bound i, _), (Free (f, _), _)) =>
          (clashB context binders i f; raise Unification_Types.UNIF))
  handle exn =>
    if Exn.is_interrupt exn then Exn.reraise exn else
    let
      (*replace all Bounds by Frees to make hint matching possible*)
      val (s', t') = Unification_Util.replace_binders binders (s, t)
      val ctxt = Context.proof_of context
      val _ = @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
          Pretty.str "Failed to pattern unify; trying hints for ",
          Util.pretty_terms ctxt [s', t']
        ]
        |> Pretty.string_of)
      val hint_results = try_hints_fun context Pattern.match hints_unifier hints env (s', t')
    in
      case Seq.pull hint_results of
        SOME (res, _) => res
      | NONE =>
          (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
              Pretty.str "Unification failed for ",
              Util.pretty_terms ctxt [s', t']
            ]
            |> Pretty.string_of);
          raise exn)
    end

and unif_args try_hints_fun hints hints_unifier context binders ss ts env thm =
  let
    val ctxt = Context.proof_of context
  (* fun combine thm (env, thm_arg) =
      let val (thm', thm_arg') = apply2 (Util.norm_thm_types ctxt env) (thm, thm_arg)
      in (env, Hints.combination thm' thm_arg') end
    fun unif_fold tpair (env, thm) =
      unif try_hints_fun hints hints_unifier context binders tpair env
      |> combine thm
  in fold unif_fold (ss ~~ ts) (env, thm) end *)
    fun unif_arg tpair (env, thms) =
       unif try_hints_fun hints hints_unifier context binders tpair env
       ||> (fn thm => thm :: thms)
    val (env', thms) = fold unif_arg (ss ~~ ts) (env, []) ||> rev
    val norm_thm = Util.norm_thm_types ctxt env'
    fun combine thm_arg thm = norm_thm thm_arg |> Hints.combination thm
  in (env', fold combine thms (norm_thm thm)) end

and rigidrigid try_hints_fun hints hints_unifier context (env, binders, t, (b, Tb), ss, ts) =
  let val (a, Ta) = (if is_Const t then dest_Const else dest_Free) t
  in
    if a <> b then (clash context a b; raise Unification_Types.UNIF)
    else
      let
        val env' = Util.unify_types context (Ta, Tb) env
        val thm = Hints.reflexive_term context t
      in unif_args try_hints_fun hints hints_unifier context binders ss ts env' thm end
  end

and rigidrigidB try_hints_fun hints hints_unifier context (env, binders, i, j, ss, ts) =
  if i <> j then (clashBB context binders i j; raise Unification_Types.UNIF)
  else
    let val thm = Util.binder_free binders i |> Hints.reflexive_term context
    in unif_args try_hints_fun hints hints_unifier context binders ss ts env thm end

and flexrigid context (params as (env, binders, F, Fty, is, t)) =
  if occurs (F, t, env) then
    (ocheck_fail context (F, t, binders, env); raise Unification_Types.UNIF)
  else
    let
      val var_app = app_free env binders F Fty is
      val binder_types = map (snd o fst) binders
      val env' = Util.unify_types context
        (fastype_of1 (binder_types, var_app), Envir.fastype env binder_types t) env
      val (u, env'') = proj context (t, env', binders, is)
      val env''' = Envir.update ((F, Fty), mkabs (binders, is, u)) env''
      val thm = Hints.reflexive_term context var_app
    in (env''', thm) end
    handle (exn as Unification_Types.UNIF) => (proj_fail context params; raise exn)

fun unif_core try_hints_fun hints hints_unifier context binders (s, t) =
  let val ctxt = Context.proof_of context
  in
    @{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.block [
        Pretty.str "Higher-order pattern unifying ",
        Util.pretty_terms ctxt [s, t]
      ]
      |> Pretty.string_of);
    unif try_hints_fun hints hints_unifier context binders (s, t)
  end

(*higher-order pattern unification with hints from context*)
fun unify_hints context =
  unif_core Hints.try_hints (Hints.gen_hint_list (Context.proof_of context)) unify_hints context []

(*higher-order pattern unification without hints*)
fun unify context = unif_core (K o K o K o K o K o K Seq.empty) [] unify context []

end
