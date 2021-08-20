(*  Title:      Unification_Hints/first_order_unification.ML
    Author:     Kevin Kappelmann, Paul Bachmann

First-order unification with hints (see unification_hints.ML).
*)
signature FIRST_ORDER_UNIFICATION =
sig

  val unify : Unifier_Types.unifier 
  val unify_hints : Unifier_Types.unifier

end

structure First_Order_Unification : FIRST_ORDER_UNIFICATION =
struct

structure Hints = Unification_Hints

(*occurs check*)
fun contains_var v (Var (x, _)) = x = v
  | contains_var v (t1 $ t2) = contains_var v t1 orelse contains_var v t2
  | contains_var v (Abs (_, _, t)) = contains_var v t
  | contains_var _ _ = false

fun unify_core try_hints_fun hints hints_unifier context (t1, t2)
  (Envir.Envir {tenv, tyenv, maxidx}) =
let
  val ctxt = Context.proof_of context
  (*standard first-order unifier that calls try_hint on failure*)
  fun unif try_hints_fun env (t1, t2) =
    (case (t1, t2) of
      (Free (x, Tx), Free (y, Ty)) =>
        if x = y then
          (Pattern.unify_types context (Tx, Ty) env,
            Hints.reflexive_term context t1)
        else raise Pattern.Unif
    | (Const (x, Tx), Const (y, Ty)) =>
        if x = y then
          (Pattern.unify_types context (Tx, Ty) env,
            Hints.reflexive_term context t1)
        else raise Pattern.Unif
    | (f $ x, g $ y) =>
        let
          val (env', thm_fg) = unif try_hints_fun env (f, g)
          val (env'', thm_xy) = unif try_hints_fun env' (x, y)
        in (env'', Hints.combination thm_fg thm_xy) end
    | (t1 as Var (x, Tx), _) => 
        (unif try_hints_fun env (Envir.norm_term_same env t1, t2)
        handle Same.SAME =>
          (unif try_hints_fun env (t1, Envir.norm_term_same env t2)
          handle Same.SAME =>
            let val update_env =
              (*unifying x=x ==> no new term substitution necessery*)
              if is_Var t2 andalso x = fst (dest_Var t2) then I
              (*open term and occurs check*)
              else if Term.is_open t2 orelse contains_var x t2 then
                (Logger.debug ctxt
                  (fn ts => Pretty.block [
                      Pretty.str
                        "Failed to unify (occurs check or open term) ",
                      Utils.pretty_terms ctxt ts
                    ]
                    |> Pretty.writeln)
                  [t1, t2];
                raise Pattern.Unif)
              (*insert new substitution x |-> t2*)
              else Envir.update ((x, Tx), t2)
            in
              (Pattern.unify_types context (Tx, fastype_of t2) env,
                Hints.reflexive_term context t1)
              |>> update_env
            end))
    | (_, Var _) => unif try_hints_fun env (t2, t1) ||> Hints.symmetric
    (*TODO: fixme - does not work with theorem generation*)
    (* | (Bound i, Bound j) =>
        if i = j then (env, reflexive_term context (Bound i))
        else raise Pattern.Unif
    | (Abs (_, ty1, t1), Abs (_, ty2, t2)) =>
        unif try_hints_fun (Pattern.unify_types context (ty1, ty2) env) (t1, t2)
    | (t1, Abs (_, _, t2)) => unif try_hints_fun env (t2,(incr_boundvars 1 t1)$(Bound 0))
    | (Abs (_, _, t1), t2) => unif try_hints_fun env (t1,(incr_boundvars 1 t2)$(Bound 0)) *)
    | _ => raise Pattern.Unif)
    handle exn => if Exn.is_interrupt exn then Exn.reraise exn else 
      let
        val _ = Logger.debug ctxt
          (fn ts => Pretty.block [
              Pretty.str
                "Failed to (standard) unify; trying hints for ",
              Utils.pretty_terms ctxt ts
            ]
            |> Pretty.writeln)
          [t1, t2]
        val hint_results =
          try_hints_fun context Pattern.match hints_unifier hints env (t1, t2)
      in
        case Seq.pull hint_results of 
          SOME (res,_) => res
        | NONE =>
            (Logger.debug ctxt
              (fn ts => Pretty.block [
                  Pretty.str
                    "Unification failed for ",
                  Utils.pretty_terms ctxt ts
                ]
                |> Pretty.writeln)
              [t1, t2];
            raise exn)
      end
in
  let
    val _ = Logger.debug ctxt
      (fn ts =>
        Pretty.block [Pretty.str "First-order unifying ",
          Utils.pretty_terms ctxt ts]
        |> Pretty.writeln)
      [t1, t2]
    val (env_res, thm) = unif try_hints_fun
      (Envir.Envir {
        tenv = tenv,
        tyenv = tyenv,
        maxidx = Int.max (maxidx,
          Int.max (maxidx_of_term t1, maxidx_of_term t2))
      })
      (t1, t2)
  in (env_res, thm) end
end

(*first-order unification with hints*)
fun unify_hints context =
  unify_core Hints.try_hints
    (Hints.gen_hint_list (Context.proof_of context)) unify_hints context

(*standard first-order unification without hints*)
fun unify context = unify_core (K o K o K o K o K o K Seq.empty) []
  unify context

end