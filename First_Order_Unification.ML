(* First Order Unification *)
signature First_Order_Unification =
sig

  type hint = (term * term) * Envir.tenv * thm

  exception Unif of term * term
  exception Occurs_Check of term
  exception Matching_Hints of ((term * term) * hint * exn) list * exn

  val first_order_unify : Proof.context -> term * term -> Envir.env -> (Envir.env * thm)
  val first_order_unify_h : Proof.context -> term * term -> Envir.env -> (Envir.env * thm)

end

structure Fou : First_Order_Unification =
struct

type hint = (term * term) * Envir.tenv * thm

datatype unif_option = ENV of Envir.env * thm | MATCH of (term * term) * hint * exn
val is_env = fn ENV _ => true | _ => false

exception Unif of term * term
exception Occurs_Check of term
exception Matching_Hints of ((term * term) * hint * exn) list * exn

val hint_trace = Attrib.setup_config_bool @{binding \<open>hint_trace\<close>} (K false)

(*theorems reflexity, combination and symmetry*)
val reflexive = @{thm Pure.reflexive}
val combination = Thm.axiom @{theory} "Pure.combination"
val symmetric = @{thm Pure.symmetric}

(*flips a thm using symmetry*)
fun flip_thm thm = symmetric OF [thm]

(*instantiates the first type variable in th with typ*)
fun instantiate_type_var ctxt typ thm =
  Thm.instantiate ([(hd (Term.add_tvars (Thm.full_prop_of thm) []), Thm.ctyp_of ctxt typ)], []) thm

(*instantiates Pure.reflexive with [t/x_0]*)
fun inst_refl ctxt t =
  let val renamed_refl = instantiate_type_var ctxt (type_of t) reflexive
      val var =  (hd (Term.add_vars (Thm.full_prop_of renamed_refl) []))
      val ct = Thm.cterm_of ctxt t
  in infer_instantiate_types ctxt [(var,ct)] renamed_refl end

(*map function over bound indices, from pattern.ML*)
fun mapbnd f =
  let fun mpb d (Bound (i))    = if i < d then Bound(i) else Bound(f(i-d)+d)
        | mpb d (Abs (s,T,t))  = Abs(s,T,mpb(d+1) t)
        | mpb d (u1 $ u2)      = (mpb d u1)$(mpb d u2)
        | mpb _ atom           = atom
  in mpb 0 end

(*increases all bound indices in a term by 1*)
val incr = mapbnd (fn i => i+1)

(*occurs check*)
fun contains_var v =
  fn Var (x,_)   => x = v
  |  t1 $ t2     => contains_var v t2 orelse contains_var v t1
  |  Abs (_,_,t) => contains_var v t
  |  _           => false

(*increase index of all Vars in term by n*)
fun incr_idx n =
   fn Var ((name,idx),T) => Var ((name,idx+n),T)
   |  Abs (x,T,t)        => Abs (x,T,incr_idx n t)
   |  t1 $ t2            => incr_idx n t1 $ incr_idx n t2
   |  t                  => t

(*generates a hint from a theorem,
  returns (SOME hint,"") if successfull,
  (NONE,thm_name) otherwise*)
fun gen_hint thm = (SOME
  (thm |> Thm.concl_of
       |> (fn (Const ("Pure.eq",_) $ t1 $ t2) => (Envir.eta_contract t1,Envir.eta_contract t2)),
  (thm |> Thm.prems_of
       |> map (fn ((Const ("Pure.eq",_) $ Var (vn,typ) $ t)) => (vn,(typ,Envir.eta_contract t)))
       |> fold (fn tup => fn env => Vartab.update_new tup env)) Vartab.empty, Drule.eta_contraction_rule thm),"")
  handle Match => (NONE,Thm.derivation_name thm)

(*unifies Ts, returns Envir.Envir*)
fun ty_unify ctxt Ts (Envir.Envir {maxidx,tenv,tyenv}) =
  let val (tyenv',_) = Sign.typ_unify (Proof_Context.theory_of ctxt) Ts (tyenv,maxidx)
  in Envir.Envir {maxidx = maxidx, tenv = tenv, tyenv = tyenv'} end

(*generates a list of hints from named theorems "hints"*)
fun gen_hint_list ctxt =
  let
    val (hs,strs) =
      Proof_Context.get_thms ctxt "hints"
        |> map gen_hint
        |> ListPair.unzip
    val thm_strs = filter (fn x => x <> "") strs
    val _ =
      if null thm_strs then ()
      else Log.info ctxt tracing
             ("These theorems cannot be used as hints: \n"^ String.concatWith ", " thm_strs)
  in
    hs |> filter Option.isSome
       |> map Option.valOf
       |> rev
  end

(*converts Envir into lists of var to cterm and tvar to ctype mappings*)
fun env_lists (Envir.Envir {tenv,tyenv,...}) ctxt =
  (map (fn (xi,(S,T)) => ((xi,S),Thm.ctyp_of ctxt T)) (Vartab.dest tyenv),
   map (fn (xi,(T,t)) => ((xi,T),Thm.cterm_of ctxt t)) (Vartab.dest tenv))

(*converts Envir into var to cterm list without type (for infer_instantiate)*)
fun envir_to_ct_map ctxt env = env_lists env ctxt |> snd |> map (fn ((a,_),c) => (a,c))

(*converts idx, type and term environment into Envir*)
fun idx_envs_to_envir idx (tyenv,tenv) = Envir.Envir {tyenv=tyenv,tenv=tenv,maxidx=idx}

(*converts Envir into type and term environment*)
fun envir_to_envs (Envir.Envir {tyenv,tenv,...}) = (tyenv,tenv)

(*discharges n prems by applying reflexivity*)
fun discharge_prems thm =
  fn 0 => thm
  |  n => discharge_prems (thm OF [reflexive]) (n-1)

fun unif ctxt env =
  fn
    (Free(x,Tx),Free(y,Ty)) =>
      if x=y then
        let
          val env' = ty_unify ctxt (Tx,Ty) env
        in
          (env',inst_refl ctxt (Free (x,Envir.norm_type (Envir.type_env env') Tx)))
        end
      else raise Unif (Free(x,Tx),Free(y,Ty))
  | (Const(x,Tx),Const(y,Ty)) =>
      if x=y then
        let
          val env' = ty_unify ctxt (Tx,Ty) env
        in
          (env',inst_refl ctxt (Const (x,Envir.norm_type (Envir.type_env env') Tx)))
        end
      else raise Unif (Const(x,Tx),Const(y,Ty))
  | (f $ t1,g $ t2) =>
      let
        val (env',thm_fg) = unif ctxt env (f,g)
        val (env'',thm_xy) = unif ctxt env' (Envir.norm_term env' t1, Envir.norm_term env' t2)
      in
        (env'',
         combination OF [infer_instantiate ctxt (envir_to_ct_map ctxt env'') thm_fg,
                         infer_instantiate ctxt (envir_to_ct_map ctxt env'') thm_xy])
      end
    | (Var(x,Tx),Var(y,Ty)) =>
        let
          val env' = ty_unify ctxt (Ty,Tx) env
          val norm_tyenv' = Envir.norm_type (Envir.type_env env')
        in
         (if x=y then env' else Envir.update ((x,norm_tyenv' Tx),Var(y,norm_tyenv' Ty)) env',
          inst_refl ctxt (Var(y,norm_tyenv' Ty)))
        end
    | (Var(x,Tx),t) =>
        if Term.is_open t then raise Unif (Var(x,Tx),t)
         else if contains_var x t then raise Occurs_Check (Var(x,Tx)) else
          (case Envir.lookup env (x,Tx) of
              NONE    => let val env' = ty_unify ctxt (fastype_of t,Tx) env in
                          (Envir.update ((x,Envir.norm_type (Envir.type_env env') Tx),t) env',inst_refl ctxt t) end
            | SOME t' => if Envir.aeconv (t',t) then (env,inst_refl ctxt t) else unif ctxt env (t',t))
    | (t,Var(x,Tx)) =>
        if Term.is_open t then raise Unif (t,Var(x,Tx))
         else if contains_var x t then raise Occurs_Check (Var(x,Tx)) else
          (case Envir.lookup env (x,Tx) of
              NONE    => let val env' = ty_unify ctxt (fastype_of t,Tx) env in
                          (Envir.update ((x,Envir.norm_type (Envir.type_env env') Tx),t) env',inst_refl ctxt t) end
            | SOME t' => if Envir.aeconv (t',t) then (env,inst_refl ctxt t) else unif ctxt env (t,t'))
    | (Abs(_,T1,t1),Abs(_,T2,t2)) => unif ctxt (ty_unify ctxt (T1,T2) env) (t1,t2)
    | (Bound i,Bound j)           => if i=j then (env,inst_refl ctxt (Bound i)) else raise Unif (Bound i,Bound j)
    | (t1,Abs(_,_,t2))            => unif ctxt env (t2,(incr t1)$(Bound 0))
    | (Abs(_,_,t1),t2)            => unif ctxt env (t1,(incr t2)$(Bound 0))
    | (t1,t2) => raise Unif (t1,t2)

fun first_order_unify ctxt (term1,term2) env =
  unif ctxt env
   (Envir.norm_term env term1 |> Envir.eta_contract,
    Envir.norm_term env term2 |> Envir.eta_contract)

fun first_order_unify_envir ctxt ts env =
  fst (first_order_unify ctxt ts env)

(*tries to apply a hint to solve unification of (t1=?t2),
  Vars in hint are renamed to avoid naming conflicts during matching,
  returns SOME (Envir,thm) if successfull,
  unifies resulting unification problems using unif*)
fun try_hint ctxt unif (Envir.Envir {maxidx,tenv,tyenv}) (t1,t2) (hint as ((h1_raw,h2_raw),hint_tenv,hint_thm)) =
  let
    val pmatch = Pattern.match (Proof_Context.theory_of ctxt)
    val (h1,h2) = (incr_idx (maxidx+1) h1_raw,incr_idx (maxidx+1) h2_raw)
    val maxidx_new = Int.max (maxidx,Int.max (maxidx_of_term h1,maxidx_of_term h2))
    val unif_envs = (tyenv,tenv)
    val match_envir =
      (pmatch (h2,t2) (pmatch (h1,t1) unif_envs)
        handle Pattern.MATCH => pmatch (h2,t1) (pmatch (h1,t2) unif_envs))
      |> idx_envs_to_envir maxidx_new
    val hint_thm_matched =
      infer_instantiate ctxt
        (envir_to_ct_map ctxt match_envir)
        (Thm.incr_indexes (maxidx+1) hint_thm)
    fun foldfun ((s,i),(typ,term)) envir =
      unif ctxt
        (Envir.norm_term match_envir (incr_idx (maxidx+1) term),
         Envir.lookup match_envir ((s,i+maxidx+1),typ) |> Option.valOf) envir
        |> fst
    val (match_tyenv,match_tenv) = envir_to_envs match_envir
    val envir_return =
      Vartab.fold foldfun hint_tenv
        (Envir.Envir {maxidx=maxidx_new,tenv=match_tenv,tyenv=match_tyenv})
  in
    SOME (ENV (envir_return,infer_instantiate ctxt (envir_to_ct_map ctxt envir_return) hint_thm_matched))
  end
    handle Pattern.MATCH => NONE
    | Unif ts => let val _ = Log.debug ctxt tracing "matched"
                 in SOME (MATCH ((t1,t2),hint,Unif ts)) end

(* tries to apply a hint to solve unification of (t1=?t2) using first order unification,
   Vars in hint are renamed to avoid naming conflicts during unification,
   returns SOME (Envir,thm) if successfull *)
fun try_hint_unif ctxt (unif_envir as Envir.Envir {maxidx,...}) (t1,t2) ((h1_raw,h2_raw),hint_tenv,hint_thm) =
    let val unify = first_order_unify_envir ctxt
        val (h1,h2) = (incr_idx (maxidx+1) h1_raw,incr_idx (maxidx+1) h2_raw)
        val maxidx_new = Int.max (maxidx,Int.max (maxidx_of_term h1,maxidx_of_term h2))
        val match_envir = (unify (h2,t2) (unify (h1,t1) unif_envir)
          handle _ => unify (h2,t1) (unify (h1,t2) unif_envir))
        val hint_thm_matched = infer_instantiate ctxt (envir_to_ct_map ctxt match_envir) (Thm.incr_indexes (maxidx+1) hint_thm)
        fun foldfun ((s,i),(typ,term)) envir =
          first_order_unify_envir ctxt (Envir.norm_term match_envir (incr_idx (maxidx+1) term),Envir.lookup match_envir ((s,i+maxidx+1),typ) |> Option.valOf) envir
        val envir_return = Vartab.fold foldfun hint_tenv (Envir.Envir {maxidx=maxidx_new,tenv=Envir.term_env match_envir,tyenv=Envir.type_env match_envir})
    in SOME (envir_return,infer_instantiate ctxt (envir_to_ct_map ctxt envir_return) hint_thm_matched)
end handle _ => NONE

(* tries to apply a hint to solve unification of (t1=?t2) using kernel unification,
   Vars in hint are renamed to avoid naming conflicts during unification,
   returns SOME (Envir,thm) if successfull *)
fun try_hint_unif_kernel ctxt (unif_envir as Envir.Envir {maxidx,...}) (t1,t2) ((h1_raw,h2_raw),hint_tenv,hint_thm) =
    let val unify = Pattern.unify (Context.Proof ctxt)
        val (h1,h2) = (incr_idx (maxidx+1) h1_raw,incr_idx (maxidx+1) h2_raw)
        val maxidx_new = Int.max (maxidx,Int.max (maxidx_of_term h1,maxidx_of_term h2))
        val match_envir = (unify (h2,t2) (unify (h1,t1) unif_envir)
          handle _ => unify (h2,t1) (unify (h1,t2) unif_envir))
        val hint_thm_matched =
          infer_instantiate ctxt (envir_to_ct_map ctxt match_envir) (Thm.incr_indexes (maxidx+1) hint_thm)
        fun foldfun ((s,i),(typ,term)) envir =
          unify (Envir.norm_term match_envir (incr_idx (maxidx+1) term),Envir.lookup match_envir ((s,i+maxidx+1),typ) |> Option.valOf) envir
        val envir_return = Vartab.fold foldfun hint_tenv (Envir.Envir {maxidx=maxidx_new,tenv=Envir.term_env match_envir,tyenv=Envir.type_env match_envir})
    in SOME (envir_return,infer_instantiate ctxt (envir_to_ct_map ctxt envir_return) hint_thm_matched)
end handle _ => NONE


(*first order unification with hints*)
fun hint_unify hints ctxt (term1,term2) env =
let
  (*assembles list of matching hints from list, drops first i hints*)
  fun apply_hints ctxt envir (t1,t2) i =
    map Option.valOf
      o drop i
      o filter Option.isSome
      o map (fn h => try_hint ctxt (hint_unify hints) envir (t1,t2) h)

  (*unifies terms, calls try_hint upon failure*)
  fun unif envir (t1,t2) =
  (case (t1,t2) of
      (Free(x,Tx),Free(y,Ty)) =>
        if x=y then
          let
            val env' = ty_unify ctxt (Ty,Tx) envir
          in
            (env',inst_refl ctxt (Free(x,Envir.norm_type (Envir.type_env env') Tx))) end
        else raise Unif (Free(x,Tx),Free(y,Ty))
    | (Const(x,Tx),Const(y,Ty)) =>
        if x=y then
          let
            val env' = ty_unify ctxt (Ty,Tx) envir
          in
            (env',inst_refl ctxt (Const(x,Envir.norm_type (Envir.type_env env') Tx))) end
        else raise Unif (Const(x,Tx),Const(y,Ty))
    | (f $ t1,g $ t2) =>
        let
          val (env',thm_fg) = unif envir (f,g)
          val (env'',thm_xy) = unif env' (Envir.norm_term env' t1, Envir.norm_term env' t2)
        in
          (env'',
           combination OF [infer_instantiate ctxt (envir_to_ct_map ctxt env'') thm_fg,
                           infer_instantiate ctxt (envir_to_ct_map ctxt env'') thm_xy])
        end
    | (Var(x,Tx),Var(y,Ty)) =>
        let
          val env' = ty_unify ctxt (Ty,Tx) envir
          val norm_tyenv' = Envir.norm_type (Envir.type_env env')
        in
         (if x=y then env' else Envir.update ((x,norm_tyenv' Tx),Var(y,norm_tyenv' Ty)) env',
          inst_refl ctxt (Var(y,norm_tyenv' Ty)))
        end
    | (Var(x,Tx),t) =>
        if Term.is_open t then raise Unif (Var(x,Tx),t)
        else if contains_var x t then raise Occurs_Check (Var(x,Tx))
        else
          (case Envir.lookup envir (x,Tx) of
             NONE    =>
               let val env' = ty_unify ctxt (fastype_of t,Tx) envir
               in
                 (Envir.update ((x,Envir.norm_type (Envir.type_env env') Tx),t) env',
                  inst_refl ctxt t)
               end
           | SOME t' =>
               if Envir.aeconv (t',t) then (envir,inst_refl ctxt t')
               else unif envir (t',t))
    | (t,Var(x,Tx)) =>
        if Term.is_open t then raise Unif (t,Var(x,Tx))
         else if contains_var x t then raise Occurs_Check (Var(x,Tx))
         else
           (case Envir.lookup envir (x,Tx) of
              NONE    =>
                let val env' = ty_unify ctxt (fastype_of t,Tx) envir
                in
                  (Envir.update ((x,Envir.norm_type (Envir.type_env env') Tx),t) env',
                   inst_refl ctxt t)
                end
            | SOME t' =>
                if Envir.aeconv (t,t') then (envir,inst_refl ctxt t)
                else unif envir (t,t'))
    | (Bound i,Bound j) =>
        if i=j then (envir,inst_refl ctxt (Bound i))
        else raise Unif (Bound i,Bound j)
    | (Abs(_,ty1,t1),Abs(_,ty2,t2)) => unif (ty_unify ctxt (ty1,ty2) envir) (t1,t2)
    | (t1,Abs(_,_,t2))              => unif envir (t2,(incr t1)$(Bound 0))
    | (Abs(_,_,t1),t2)              => unif envir (t1,(incr t2)$(Bound 0))
    | (t1,t2) => raise Unif (t1,t2))
   handle exn =>
     let
       val hint_match_list = (apply_hints ctxt envir (Envir.norm_term envir t1,Envir.norm_term envir t2) 0 hints)
       val hint_list = filter is_env hint_match_list |> map (fn ENV x => x)
       val matching_list = filter (not o is_env) hint_match_list |> map (fn MATCH x => x)
     in
       if null hint_match_list then raise exn else
        if null hint_list then raise Matching_Hints (matching_list,exn)
        else hd hint_list end
in
  let val (sigma,thm) = unif
    (Envir.Envir
      {tenv   = Envir.term_env env,
       tyenv  = Envir.type_env env,
       maxidx = Int.max (Envir.maxidx_of env,Int.max (maxidx_of_term term1,maxidx_of_term term2))})
    (term1 |> Envir.norm_term env |> Envir.eta_contract,
     term2 |> Envir.norm_term env |> Envir.eta_contract)
  in (sigma, discharge_prems thm (Thm.nprems_of thm))
  end
end

fun print_matched_hint ctxt (t1,t2,thm) =
  "Terms "
    ^ Pretty.string_of (pretty_term ctxt t1) ^ ", "
    ^ Pretty.string_of (pretty_term ctxt t2) ^ " matched hint: "
    ^ Pretty.string_of (pretty_thm ctxt thm)


fun print_matching_hints ctxt hs =
  let val _ = tracing "These hints matched but the resulting unification could not be solved:"
  in fold (fn ((t1,t2),(_,_,thm),exn) => fn _ =>
        (tracing (print_matched_hint ctxt (t1,t2,thm));
         Log.debug ctxt (tracing o (fn str => "Exception raised:\n"^str) o @{make_string}) exn)) hs ()
  end

fun first_order_unify_h ctxt ts env =
  hint_unify (gen_hint_list ctxt) ctxt ts env
  handle Matching_Hints (hs,exn) =>
    let val _ = Log.info ctxt (print_matching_hints ctxt) hs
    in raise exn
    end


end
