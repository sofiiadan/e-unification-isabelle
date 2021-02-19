(*First Order Unification*)
signature First_Order_Unification = 
sig
  type hint = (term * term) * Envir.tenv * thm
  exception Unif of term * term
  exception Occurs_Check of term
  exception Malformed_Hint of string
  exception Matching_Hints of ((term * term) * hint) list * exn
  val first_order_unify :
    Proof.context -> term * term -> Envir.env -> Envir.env
  val first_order_unify_thm :
    Proof.context -> term * term -> Envir.env -> (Envir.env * thm)
  exception Hint_Unif of term * term * hint
  val gen_hint_list : Proof.context -> hint list
  val hint_unify :
    Proof.context -> hint list ->  term * term -> Envir.env -> (Envir.env * thm)
  val first_order_unify_h :
    Proof.context -> term * term -> Envir.env -> (Envir.env * thm)
  val hint_trace : bool Config.T
end

structure Fou : First_Order_Unification =
struct

type hint = (term * term) * Envir.tenv * thm
datatype unif_option = ENV of Envir.env * thm | MATCH of (term * term) * hint
val is_env = fn ENV _ => true | _ => false

exception Unif of term * term
exception Occurs_Check of term
exception Malformed_Hint of string
exception Hint_Unif of term * term * hint
exception Matching_Hints of ((term * term) * hint) list * exn

val hint_trace = Attrib.setup_config_bool @{binding \<open>hint_trace\<close>} (K false)

(* theorems reflexity, combination and symmetry *)
val reflexive = @{thm Pure.reflexive}
val combination = Thm.axiom @{theory} "Pure.combination"
val symmetric = @{thm Pure.symmetric}

fun flip_thm thm = symmetric OF [thm]

(* Instantiate the first type variable in th with typ *)
fun instantiate_type_var ctxt typ thm =
  Thm.instantiate ([(hd (Term.add_tvars (Thm.full_prop_of thm) []), Thm.ctyp_of ctxt typ)], []) thm

(* instantiates Pure.reflexive with [t/x_0] *)
fun instantiate_refl ctxt t =
  let val renamed_refl = instantiate_type_var ctxt (type_of t) reflexive
      val xVar =  (hd (Term.add_vars (Thm.full_prop_of renamed_refl) []))
  in infer_instantiate_types ctxt [(xVar,Thm.cterm_of ctxt t)] renamed_refl
  end

(*map function over bound indices, from pattern.ML*)
fun mapbnd f =
  let fun mpb d (Bound (i))    = if i < d then Bound(i) else Bound(f(i-d)+d)
        | mpb d (Abs (s,T,t))  = Abs(s,T,mpb(d+1) t)
        | mpb d (u1 $ u2)      = (mpb d u1)$(mpb d u2)
        | mpb _ atom           = atom
  in mpb 0
  end

val incr = mapbnd (fn i => i+1)

(*Occurs check for first_order_unify*)
fun contains_var v =
  fn Var (x,_)   => x = v
  |  t1 $ t2     => contains_var v t2 orelse contains_var v t1
  |  Abs (_,_,t) => contains_var v t
  |  _           => false

(* increase index of all Vars in term by n *)
fun incr_idx n =
   fn Var ((name,idx),typ) => Var ((name,idx+n),typ)
   |  Abs (s,T,t) => (Abs(s,T,incr_idx n t))
   |  t1 $ t2 => incr_idx n t1 $ incr_idx n t2
   |  t => t

fun gen_hint thm = (SOME
  (thm |> Thm.concl_of
       |> (fn (Const ("Pure.eq",_) $ t1 $ t2) => (Envir.eta_contract t1,Envir.eta_contract t2)),
  (thm |> Thm.prems_of
       |> map (fn ((Const ("Pure.eq",_) $ Var (vn,typ) $ t)) => (vn,(typ,Envir.eta_contract t)))
       |> fold (fn tup => fn env => Vartab.update_new tup env)) Vartab.empty, Drule.eta_contraction_rule thm),"")
  handle Match => (NONE,Thm.derivation_name thm)

fun strings_flat (x::xs) = fold (fn curr => fn acc => acc^", "^curr) xs x

fun unzip l = (map fst l, map snd l)

(* unifies typs, returns Envir.Envir *)
fun ty_unify ctxt typs (Envir.Envir {maxidx,tenv,tyenv}) =
  let val (new_tyE,_) = Sign.typ_unify (Proof_Context.theory_of ctxt) typs (tyenv,maxidx)
  in Envir.Envir {maxidx = maxidx, tenv = tenv, tyenv = new_tyE}
  end



(* generates a list of hints from named theorems "hints" *)
fun gen_hint_list ctxt =
  let val (hs,strs) = Proof_Context.get_thms ctxt "hints" |> map gen_hint |> unzip
      val thmStrs = filter (fn x => x <> "") strs
      val _ = if null thmStrs then ()
        else Log.info ctxt tracing ("The following theorems cannot be used as hints: "^ strings_flat thmStrs)
  in hs |> filter Option.isSome
        |> map Option.valOf
        |> rev
  end

(* converts Envir into lists of var to cterm and tvar to ctype mappings *)
fun env_lists (Envir.Envir {tenv,tyenv,...}) ctxt =
  let fun ctyp (i_n,(sort,ty)) = ((i_n,sort),Thm.ctyp_of ctxt ty)
      fun ctrm (i_n,(typ,t)) = ((i_n,typ),Thm.cterm_of ctxt t)
  in (map ctyp (Vartab.dest tyenv), map ctrm (Vartab.dest tenv))
  end

(* converts Envir into var to cterm list without type (for infer_instantiate) *)
fun envlist ctxt env = env_lists env ctxt |> snd |> map (fn ((a,_),c) => (a,c))
(* converts idx, type and term environment into Envir *)
fun idx_envs_to_envir idx (ty,te) = Envir.Envir {tyenv=ty,tenv=te,maxidx=idx}
(* converts Envir into type and term environment *)
fun envir_to_env_tup (Envir.Envir {tyenv,tenv,...}) = (tyenv,tenv)

(* discharges n prems by applying reflexivity *)
fun discharge_prems thm =
  fn 0 => thm | n => discharge_prems (thm OF [reflexive]) (n-1)

fun unif ctxt envir (t1,t2) =
  (case (t1,t2) of
      (Free(x,tyx),Free(y,tyy)) =>
        if x=y then
          let val new_tenv = ty_unify ctxt (tyx,tyy) envir
          in (new_tenv,instantiate_refl ctxt (Free(x,Envir.norm_type (Envir.type_env new_tenv) tyx))) end
        else raise Unif (Free(x,tyx),Free(y,tyy))
    | (Const(x,tyx),Const(y,tyy)) =>
        if x=y then
          let val new_tenv = ty_unify ctxt (tyx,tyy) envir
          in (new_tenv,instantiate_refl ctxt (Const(x,Envir.norm_type (Envir.type_env new_tenv) tyx))) end
        else raise Unif (Const(x,tyx),Const(y,tyy))
    | (f $ t1,g $ t2) =>
        let val (envir',thm_fg) = unif ctxt envir (f,g)
            val (envir'',thm_xy) = unif ctxt envir' (Envir.norm_term envir' t1, Envir.norm_term envir' t2)
        in (envir'', combination OF [infer_instantiate ctxt (envlist ctxt envir'') thm_fg,
                              infer_instantiate ctxt (envlist ctxt envir'') thm_xy]) end
    | (Var(x,tyx),Var(y,tyy)) =>
        let val new_env = ty_unify ctxt (tyx,tyy) envir
            val new_tenv = Envir.type_env new_env in
         (if x=y then new_env
                 else Envir.update ((x,Envir.norm_type new_tenv tyx),Var(y,Envir.norm_type new_tenv tyy)) new_env,
          instantiate_refl ctxt (Var(y,Envir.norm_type new_tenv tyy))) end
    | (Var(x,tyx),t) =>
        if Term.is_open t then raise Unif (Var(x,tyx),t)
         else if contains_var x t then raise Occurs_Check (Var(x,tyx)) else
          (case Envir.lookup envir (x,tyx) of
              NONE    => let val new_env = ty_unify ctxt (fastype_of t,tyx) envir in 
                          (Envir.update ((x,Envir.norm_type (Envir.type_env new_env) tyx),t) new_env,instantiate_refl ctxt t) end
            | SOME t' => if Envir.aeconv (t',t) then (envir,instantiate_refl ctxt t) else unif ctxt envir (t',t))
    | (t,Var(x,tyx)) =>
        if Term.is_open t then raise Unif (t,Var(x,tyx))
         else if contains_var x t then raise Occurs_Check (Var(x,tyx)) else
          (case Envir.lookup envir (x,tyx) of
              NONE    => let val new_env = ty_unify ctxt (fastype_of t,tyx) envir in 
                          (Envir.update ((x,Envir.norm_type (Envir.type_env new_env) tyx),t) new_env,instantiate_refl ctxt t) end
            | SOME t' => if Envir.aeconv (t',t) then (envir,instantiate_refl ctxt t) else unif ctxt envir (t,t'))
    | (Abs(_,ty1,t1),Abs(_,ty2,t2)) => unif ctxt (ty_unify ctxt (ty1,ty2) envir) (t1,t2)
    | (Bound i,Bound j)             => if i=j then (envir,instantiate_refl ctxt (Bound i)) else raise Unif (Bound i,Bound j)
    | (t1,Abs(_,_,t2))              => unif ctxt envir (t2,(incr t1)$(Bound 0))
    | (Abs(_,_,t1),t2)              => unif ctxt envir (t1,(incr t2)$(Bound 0))
    | (t1,t2) => raise Unif (t1,t2))

fun first_order_unify ctxt (term1,term2) env =
let fun unif envir =
  fn (Free(x,tyx),Free(y,tyy)) =>
       if x=y then ty_unify ctxt (tyx,tyy) envir else raise Unif (Free(x,tyx),Free(y,tyy))
  |  (Const(x,tyx),Const(y,tyy)) =>
       if x=y then ty_unify ctxt (tyx,tyy) envir else raise Unif (Const(x,tyx),Const(y,tyy))
  |  (f $ t1,g $ t2) =>
       let val envir' = unif envir (f,g) in
       unif envir' (Envir.norm_term envir' t1, Envir.norm_term envir' t2) end (*norm weglassen \<Longrightarrow> Zirkuläre Mappings!*)
  |  (Var(x,tyx),Var(y,tyy)) =>
       if x=y then ty_unify ctxt (tyx,tyy) envir
              else let val new_env = ty_unify ctxt (tyx,tyy) envir in
                Envir.update ((x,Envir.norm_type (Envir.type_env new_env) tyx),Var(y,Envir.norm_type (Envir.type_env new_env) tyy)) new_env end (*statt tyx type lookup in envir*)
  |  (Var(x,tyx),t) =>
       if Term.is_open t then raise Unif (Var(x,tyx),t)
        else if contains_var x t then raise Occurs_Check (Var(x,tyx)) else
         (case Envir.lookup envir (x,tyx) of
             NONE    => let val new_env = ty_unify ctxt (tyx,fastype_of t) envir in 
                         Envir.update ((x,Envir.norm_type (Envir.type_env new_env) tyx),t) new_env end
           | SOME t' => if Envir.aeconv (t',t) then envir else unif envir (t',t))
  |  (t,Var(x,tyx))                => unif envir (Var(x,tyx),t)
  |  (Abs(_,ty1,t1),Abs(_,ty2,t2)) => unif (ty_unify ctxt (ty1,ty2) envir) (t1,t2)
  |  (Bound i, Bound j)            => if i=j then envir else raise Unif (Bound i, Bound j)
  |  (t1,Abs(_,_,t2))              => unif envir (t2,(incr t1)$(Bound 0))
  |  (Abs(_,_,t1),t2)              => unif envir (t1,(incr t2)$(Bound 0))
  |  (t1,t2) => raise Unif (t1,t2)
  in
    unif env
      (Envir.norm_term env term1 |> Envir.eta_contract,
       Envir.norm_term env term2 |> Envir.eta_contract) end

fun first_order_unify_thm ctxt (term1,term2) env =
  unif ctxt env
   (Envir.norm_term env term1 |> Envir.eta_contract,
    Envir.norm_term env term2 |> Envir.eta_contract)

(* tries to apply a hint to solve unification of (t1=?t2),
   Vars in hint are renamed to avoid naming conflicts during matching,
   returns SOME (Envir,thm) if successfull *)
fun try_hint ctxt (Envir.Envir {maxidx,tenv,tyenv}) (t1,t2) (hint as ((h1_raw,h2_raw),hint_tenv,hint_thm)) =
    let val pmatch = Pattern.match (Proof_Context.theory_of ctxt)
        val (h1,h2) = (incr_idx (maxidx+1) h1_raw,incr_idx (maxidx+1) h2_raw)
        val maxidx_new = Int.max (maxidx,Int.max (maxidx_of_term h1,maxidx_of_term h2))
        val unif_env_tup = (tyenv,tenv)
        val match_envir = (idx_envs_to_envir maxidx_new (pmatch (h2,t2) (pmatch (h1,t1) unif_env_tup))
          handle Pattern.MATCH => idx_envs_to_envir maxidx_new (pmatch (h2,t1) (pmatch (h1,t2) unif_env_tup)))
        val hint_thm_matched = infer_instantiate ctxt (envlist ctxt match_envir) (Thm.incr_indexes (maxidx+1) hint_thm)
        fun foldfun ((s,i),(typ,term)) envir =
          first_order_unify_thm ctxt (Envir.norm_term match_envir (incr_idx (maxidx+1) term),Envir.lookup match_envir ((s,i+maxidx+1),typ) |> Option.valOf) envir |> fst
        val envir_return = Vartab.fold foldfun hint_tenv (Envir.Envir {maxidx=maxidx_new,tenv=Envir.term_env match_envir,tyenv=Envir.type_env match_envir})
    in SOME (ENV (envir_return,infer_instantiate ctxt (envlist ctxt envir_return) hint_thm_matched)) end
    handle Pattern.MATCH => NONE | Unif _ => SOME (MATCH ((t1,t2),hint))

(* tries to apply a hint to solve unification of (t1=?t2) using first order unification,
   Vars in hint are renamed to avoid naming conflicts during unification,
   returns SOME (Envir,thm) if successfull *)
fun try_hint_unif ctxt (unif_envir as Envir.Envir {maxidx,...}) (t1,t2) ((h1_raw,h2_raw),hint_tenv,hint_thm) =
    let val unify = first_order_unify ctxt
        val (h1,h2) = (incr_idx (maxidx+1) h1_raw,incr_idx (maxidx+1) h2_raw)
        val maxidx_new = Int.max (maxidx,Int.max (maxidx_of_term h1,maxidx_of_term h2))
        val match_envir = (unify (h2,t2) (unify (h1,t1) unif_envir)
          handle _ => unify (h2,t1) (unify (h1,t2) unif_envir))
        val hint_thm_matched = infer_instantiate ctxt (envlist ctxt match_envir) (Thm.incr_indexes (maxidx+1) hint_thm)
        fun foldfun ((s,i),(typ,term)) envir =
          first_order_unify ctxt (Envir.norm_term match_envir (incr_idx (maxidx+1) term),Envir.lookup match_envir ((s,i+maxidx+1),typ) |> Option.valOf) envir
        val envir_return = Vartab.fold foldfun hint_tenv (Envir.Envir {maxidx=maxidx_new,tenv=Envir.term_env match_envir,tyenv=Envir.type_env match_envir})
    in SOME (envir_return,infer_instantiate ctxt (envlist ctxt envir_return) hint_thm_matched)
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
          infer_instantiate ctxt (envlist ctxt match_envir) (Thm.incr_indexes (maxidx+1) hint_thm)
        fun foldfun ((s,i),(typ,term)) envir =
          Pattern.unify (Context.Proof ctxt) (Envir.norm_term match_envir (incr_idx (maxidx+1) term),Envir.lookup match_envir ((s,i+maxidx+1),typ) |> Option.valOf) envir
        val envir_return = Vartab.fold foldfun hint_tenv (Envir.Envir {maxidx=maxidx_new,tenv=Envir.term_env match_envir,tyenv=Envir.type_env match_envir})
    in SOME (envir_return,infer_instantiate ctxt (envlist ctxt envir_return) hint_thm_matched)
end handle _ => NONE



(* first order unification with hints *)
fun hint_unify ctxt hints (term1,term2) env =
let 
  (* tries to apply a hint to solve unification of (t1=?t2),
   Vars in hint are renamed to avoid naming conflicts during matching,
   unifying resulting subgoal using hint unification recursively
   returns SOME (Envir,thm) if successfull *)
  fun try_hint_recursive ctxt (Envir.Envir {maxidx,tenv,tyenv}) (t1,t2) (hint as ((h1_raw,h2_raw),hint_tenv,hint_thm)) =
    let val pmatch = Pattern.match (Proof_Context.theory_of ctxt)
        val (h1,h2) = (incr_idx (maxidx+1) h1_raw,incr_idx (maxidx+1) h2_raw)
        val maxidx_new = Int.max (maxidx,Int.max (maxidx_of_term h1,maxidx_of_term h2))
        val unif_env_tup = (tyenv,tenv)
        val match_envir = (idx_envs_to_envir maxidx_new (pmatch (h2,t2) (pmatch (h1,t1) unif_env_tup))
          handle Pattern.MATCH => idx_envs_to_envir maxidx_new (pmatch (h2,t1) (pmatch (h1,t2) unif_env_tup)))
        val hint_thm_matched = infer_instantiate ctxt (envlist ctxt match_envir) (Thm.incr_indexes (maxidx+1) hint_thm)
        fun foldfun ((s,i),(typ,term)) envir =
          hint_unify ctxt hints (Envir.norm_term match_envir (incr_idx (maxidx+1) term),Envir.lookup match_envir ((s,i+maxidx+1),typ) |> Option.valOf) envir |> fst
        val envir_return = Vartab.fold foldfun hint_tenv (Envir.Envir {maxidx=maxidx_new,tenv=Envir.term_env match_envir,tyenv=Envir.type_env match_envir})
    in SOME (ENV (envir_return,infer_instantiate ctxt (envlist ctxt envir_return) hint_thm_matched)) end
    handle Pattern.MATCH => NONE | Unif _ => SOME (MATCH ((t1,t2),hint))

  (* assembles list of matching hints from list, drops first i hints*)
  fun appl_hints ctxt envir (t1,t2) i =
    map Option.valOf
      o drop i
      o filter Option.isSome
      o map (fn h => try_hint_recursive ctxt envir (t1,t2) h)

  fun unif envir (t1,t2) =
  (case (t1,t2) of
      (Free(x,tyx),Free(y,tyy)) =>
        if x=y then
          let val new_tenv = ty_unify ctxt (tyy,tyx) envir
          in (new_tenv,instantiate_refl ctxt (Free(x,Envir.norm_type (Envir.type_env new_tenv) tyx))) end
        else raise Unif (Free(x,tyx),Free(y,tyy))
    | (Const(x,tyx),Const(y,tyy)) =>
        if x=y then
          let val new_tenv = ty_unify ctxt (tyy,tyx) envir
          in (new_tenv,instantiate_refl ctxt (Const(x,Envir.norm_type (Envir.type_env new_tenv) tyx))) end
        else raise Unif (Const(x,tyx),Const(y,tyy))
    | (f $ t1,g $ t2) =>
        let val (envir',thm_fg) = unif envir (f,g)
            val (envir'',thm_xy) = unif envir' (Envir.norm_term envir' t1, Envir.norm_term envir' t2)
        in (envir'', combination OF [infer_instantiate ctxt (envlist ctxt envir'') thm_fg,
                                     infer_instantiate ctxt (envlist ctxt envir'') thm_xy]) end
    | (Var(x,tyx),Var(y,tyy)) =>
        let val new_env = ty_unify ctxt (tyy,tyx) envir
            val new_tenv = Envir.type_env new_env in
         (if x=y then new_env
                 else Envir.update ((x,Envir.norm_type new_tenv tyx),Var(y,Envir.norm_type new_tenv tyy)) new_env,
          instantiate_refl ctxt (Var(y,Envir.norm_type new_tenv tyy))) end
    | (Var(x,tyx),t) =>
        if Term.is_open t then raise Unif (Var(x,tyx),t)
         else if contains_var x t then raise Occurs_Check (Var(x,tyx)) else
          (case Envir.lookup envir (x,tyx) of
              NONE    => let val new_env = ty_unify ctxt (fastype_of t,tyx) envir in 
                          (Envir.update ((x,Envir.norm_type (Envir.type_env new_env) tyx),t) new_env,instantiate_refl ctxt t) end
            | SOME t' => if Envir.aeconv (t',t) then (envir,instantiate_refl ctxt t) else unif envir (t',t))
    | (t,Var(x,tyx)) =>
        if Term.is_open t then raise Unif (t,Var(x,tyx))
         else if contains_var x t then raise Occurs_Check (Var(x,tyx)) else
          (case Envir.lookup envir (x,tyx) of
              NONE    => let val new_env = ty_unify ctxt (fastype_of t,tyx) envir in 
                          (Envir.update ((x,Envir.norm_type (Envir.type_env new_env) tyx),t) new_env,instantiate_refl ctxt t) end
            | SOME t' => if Envir.aeconv (t',t) then (envir,instantiate_refl ctxt t) else unif envir (t,t'))
    | (Abs(_,ty1,t1),Abs(_,ty2,t2)) => unif (ty_unify ctxt (ty1,ty2) envir) (t1,t2)
    | (Bound i,Bound j)             => if i=j then (envir,instantiate_refl ctxt (Bound i)) else raise Unif (Bound i,Bound j)
    | (t1,Abs(_,_,t2))              => unif envir (t2,(incr t1)$(Bound 0))
    | (Abs(_,_,t1),t2)              => unif envir (t1,(incr t2)$(Bound 0))
    | (t1,t2) => raise Unif (t1,t2))
   handle exn =>
     let
       val hint_match_list = (appl_hints ctxt envir (Envir.norm_term envir t1,Envir.norm_term envir t2) 0 hints)
       val hint_list = filter is_env hint_match_list |> map (fn ENV x => x)
       val matching_list = filter (not o is_env) hint_match_list |> map (fn MATCH x => x)
     in
       if null hint_match_list then raise exn else
        if null hint_list then raise Matching_Hints (matching_list,exn)
        else hd hint_list end
in
  let val (sigma,thm) = unif
    (Envir.Envir {tenv=Envir.term_env env,tyenv=Envir.type_env env,maxidx=Int.max (maxidx_of_term term1,maxidx_of_term term2)})
    (term1 |> Envir.norm_term env |> Envir.eta_contract,
     term2 |> Envir.norm_term env |> Envir.eta_contract)
  in (sigma, discharge_prems thm (Thm.nprems_of thm))
  end
end

fun print_hint ctxt (t1,t2,thm) =
  "Terms "
    ^ Pretty.string_of (pretty_term ctxt t1) ^ ", "
    ^ Pretty.string_of (pretty_term ctxt t2) ^ " matched hint: "
    ^ Pretty.string_of (pretty_thm ctxt thm)

fun print_matching_hints ctxt hs =
  let val _ = tracing "These hints matched but the resulting unification could not be solved:"
  in fold (fn ((t1,t2),(_,_,thm)) => fn _ => tracing (print_hint ctxt (t1,t2,thm))) hs () end

fun first_order_unify_h ctxt ts env =
  hint_unify ctxt (gen_hint_list ctxt) ts env
  handle Matching_Hints (hs,exn) =>
    let val _ = Log.info ctxt (print_matching_hints ctxt) hs
    in raise exn
    end
    

end