(*First Order Unification*)
signature First_Order_Unification = 
sig
  exception Unif of string
  exception MalformedHint of string
  val first_order_unify :
    Proof.context -> term * term -> Envir.env -> Envir.env
  type hint = (term * term) * Envir.tenv * thm
  val gen_hint_list : Proof.context -> hint list
  val hint_unify :
    Proof.context -> hint list ->  term * term -> Envir.env -> (Envir.env * thm)
  val first_order_unify_h :
    Proof.context -> term * term -> Envir.env -> (Envir.env * thm)
end;

structure Fou : First_Order_Unification =
struct

exception Unif of string;
exception MalformedHint of string;

type hint = (term * term) * Envir.tenv * thm

(*map function over bound indices, from pattern.ML*)
fun mapbnd f =
    let fun mpb d (Bound (i))    = if i < d then Bound(i) else Bound(f(i-d)+d)
          | mpb d (Abs (s,T,t))  = Abs(s,T,mpb(d+1) t)
          | mpb d (u1 $ u2)      = (mpb d u1)$(mpb d u2)
          | mpb _ atom           = atom
    in mpb 0 end

val incr = mapbnd (fn i => i+1)

(*Occurs check for first_order_unify*)
fun contains_var v =
  fn Var (x,_)   => x = v
  |  t1 $ t2     => contains_var v t2 orelse contains_var v t1
  |  Abs (_,_,t) => contains_var v t
  |  _           => false

fun ty_unify ctxt typs (Envir.Envir {maxidx,tenv,tyenv}) =
      let val (new_tyE,_) = Sign.typ_unify (Proof_Context.theory_of ctxt) typs (tyenv,maxidx)
      in Envir.Envir {maxidx = maxidx, tenv = tenv, tyenv = new_tyE} end

fun first_order_unify ctxt (term1,term2) env =
let fun unif envir =
  fn (Free(x,tyx),Free(y,tyy)) =>
       if x=y then ty_unify ctxt (tyx,tyy) envir else raise Unif ""
  |  (Const(x,tyx),Const(y,tyy)) =>
       if x=y then ty_unify ctxt (tyx,tyy) envir else raise Unif ""
  |  (f $ t1,g $ t2) =>
       let val envir' = unif envir (f,g) in
       unif envir' (Envir.norm_term envir' t1, Envir.norm_term envir' t2) end (*norm weglassen \<Longrightarrow> Zirkuläre Mappings!*)
  |  (Var(x,tyx),Var(y,tyy)) =>
       if x=y then ty_unify ctxt (tyx,tyy) envir
              else let val new_env = ty_unify ctxt (tyx,tyy) envir in
                Envir.update ((x,Envir.norm_type (Envir.type_env new_env) tyx),Var(y,Envir.norm_type (Envir.type_env new_env) tyy)) new_env end (*statt tyx type lookup in envir*)
  |  (Var(x,tyx),t) =>
       if Term.is_open t then raise Unif ""
        else if contains_var x t then raise Unif "(Occurs Check) " else
         (case Envir.lookup envir (x,tyx) of
             NONE    => let val new_env = ty_unify ctxt (tyx,fastype_of t) envir in 
                         Envir.update ((x,Envir.norm_type (Envir.type_env new_env) tyx),t) new_env end
           | SOME t' => if Envir.aeconv (t',t) then envir else unif envir (t',t))
  |  (t,Var(x,tyx))                => unif envir (Var(x,tyx),t)
  |  (Abs(_,ty1,t1),Abs(_,ty2,t2)) => unif (ty_unify ctxt (ty1,ty2) envir) (t1,t2)
  |  (Bound i, Bound j)            => if i=j then envir else raise Unif ""
  |  (t1,Abs(_,_,t2))              => unif envir (t2,(incr t1)$(Bound 0))
  |  (Abs(_,_,t1),t2)              => unif envir (t1,(incr t2)$(Bound 0))
  |  _ => raise Unif ""
  in
    unif env
      (Envir.norm_term env term1 |> Envir.eta_contract,
       Envir.norm_term env term2 |> Envir.eta_contract) end

(* increase index of all Vars in term by n *)
fun incr_idx n =
   fn Var ((name,idx),typ) => Var ((name,idx+n),typ)
   |  Abs (s,T,t) => (Abs(s,T,incr_idx n t))
   |  t1 $ t2 => incr_idx n t1 $ incr_idx n t2
   |  t => t

fun gen_hint thm = (SOME
  (thm |> Thm.concl_of
       |> (fn Const ("HOL.Trueprop",_) $ (Const ("HOL.eq",_) $ t1 $ t2) => (t1,t2)),
  (thm |> Thm.prems_of
       |> map (fn (Const ("HOL.Trueprop", _) $ (Const ("HOL.eq",_) $ Var (vn,typ) $ t)) => (vn,(typ,Envir.eta_contract t)))
       |> fold (fn tup => fn env => Vartab.update_new tup env)) Vartab.empty, thm),"")
  handle Match => (NONE,Thm.derivation_name thm)

fun strings_flat (x::xs) = fold (fn curr => fn acc => acc^", "^curr) xs x

fun unzip l = (map fst l, map snd l)


(* generates a list of hints from named theorems "hints" *)
fun gen_hint_list ctxt =
  let val (hs,strs) = Proof_Context.get_thms ctxt "hints" |> map gen_hint |> unzip
      val thmStrs = filter (fn x => x <> "") strs
      val _ = if thmStrs = [] then ()
        else tracing ("The following theorems cannot be used as hints: "^ strings_flat thmStrs)
  in hs |> filter Option.isSome
        |> map Option.valOf end

(* converts Envir into lists of var to cterm and tvar to ctype mappings *)
fun env_lists (Envir.Envir {tenv,tyenv,...}) ctxt =
let fun ctyp (i_n,(sort,ty)) = ((i_n,sort),Thm.ctyp_of ctxt ty)
    fun ctrm (i_n,(typ,t)) = ((i_n,typ),Thm.cterm_of ctxt t)
in (map ctyp (Vartab.dest tyenv), map ctrm (Vartab.dest tenv)) end

(* converts Envir into var to cterm list without type (for infer_instantiate) *)
fun envlist ctxt env = env_lists env ctxt |> snd |> map (fn ((a,_),c) => (a,c))
(* converts idx, type and term environment into Envir *)
fun idx_envs_to_envir idx (ty,te) = Envir.Envir {tyenv=ty,tenv=te,maxidx=idx}
(* converts Envir into type and term environment *)
fun envir_to_env_tup (Envir.Envir {tyenv,tenv,...}) = (tyenv,tenv)

(* theorems reflexity and congruence *)
val rel_refl = @{thm DEADID.rel_refl}
val cong = @{thm HOL.cong}

(* tries to apply a hint to solve unification of (t1=?t2),
   Frees in hint are renamed to avoid naming conflicts during matching,
   returns SOME (Envir,thm) if successfull *)
fun try_hint ctxt (unif_envir as Envir.Envir {maxidx,...}) (t1,t2) ((h1_raw,h2_raw),hint_tenv,hint_thm) =
    let val pmatch = Pattern.match (Proof_Context.theory_of ctxt)
        val (h1,h2) = (incr_idx (maxidx+1) h1_raw,incr_idx (maxidx+1) h2_raw)
        val maxidx_new = Int.max (maxidx,Int.max (maxidx_of_term h1,maxidx_of_term h2))
        val unif_env_tup = envir_to_env_tup unif_envir
        val match_envir = (pmatch (h2,t2) (pmatch (h1,t1) unif_env_tup)
          handle Pattern.MATCH => pmatch (h2,t1) (pmatch (h1,t2) unif_env_tup))
          |> idx_envs_to_envir maxidx_new
        fun foldfun ((s,i),(typ,term)) envir =
          first_order_unify ctxt (Envir.norm_term match_envir (incr_idx (maxidx+1) term),Envir.lookup match_envir ((s,i+maxidx+1),typ) |> Option.valOf) envir
        val envir_return = Vartab.fold foldfun hint_tenv (Envir.Envir {maxidx=maxidx_new,tenv=Envir.term_env match_envir,tyenv=Envir.type_env match_envir})
    in SOME (envir_return,infer_instantiate ctxt (envlist ctxt match_envir) (Thm.incr_indexes (maxidx+1) hint_thm))
end handle Pattern.MATCH => NONE

(* tries to apply a hint to solve unification of (t1=?t2) using first order unification,
   Frees in hint are renamed to avoid naming conflicts during unification,
   returns SOME (Envir,thm) if successfull *)
fun try_hint_unif ctxt (unif_envir as Envir.Envir {maxidx,...}) (t1,t2) ((h1_raw,h2_raw),hint_tenv,hint_thm) =
    let val unify = first_order_unify ctxt
        val (h1,h2) = (incr_idx (maxidx+1) h1_raw,incr_idx (maxidx+1) h2_raw)
        val maxidx_new = Int.max (maxidx,Int.max (maxidx_of_term h1,maxidx_of_term h2))
        val match_envir = (unify (h2,t2) (unify (h1,t1) unif_envir)
          handle Unif _ => unify (h2,t1) (unify (h1,t2) unif_envir))
        fun foldfun ((s,i),(typ,term)) envir =
          first_order_unify ctxt (Envir.norm_term match_envir (incr_idx (maxidx+1) term),Envir.lookup match_envir ((s,i+maxidx+1),typ) |> Option.valOf) envir
        val envir_return = Vartab.fold foldfun hint_tenv (Envir.Envir {maxidx=maxidx_new,tenv=Envir.term_env match_envir,tyenv=Envir.type_env match_envir})
    in SOME (envir_return,infer_instantiate ctxt (envlist ctxt match_envir) (Thm.incr_indexes (maxidx+1) hint_thm))
end handle Unif _ => NONE

(* tries to apply a hint to solve unification of (t1=?t2) using kernel unification,
   Frees in hint are renamed to avoid naming conflicts during unification,
   returns SOME (Envir,thm) if successfull *)
fun try_hint_unif_kernel ctxt (unif_envir as Envir.Envir {maxidx,...}) (t1,t2) ((h1_raw,h2_raw),hint_tenv,hint_thm) =
    let val unify = Pattern.unify (Context.Proof ctxt)
        val (h1,h2) = (incr_idx (maxidx+1) h1_raw,incr_idx (maxidx+1) h2_raw)
        val maxidx_new = Int.max (maxidx,Int.max (maxidx_of_term h1,maxidx_of_term h2))
        val match_envir = (unify (h2,t2) (unify (h1,t1) unif_envir)
          handle _ => unify (h2,t1) (unify (h1,t2) unif_envir)) (* Pattern.unify can raise Pattern.Unif or UnequalLength *)
        fun foldfun ((s,i),(typ,term)) envir =
          Pattern.unify (Context.Proof ctxt) (Envir.norm_term match_envir (incr_idx (maxidx+1) term),Envir.lookup match_envir ((s,i+maxidx+1),typ) |> Option.valOf) envir
        val envir_return = Vartab.fold foldfun hint_tenv (Envir.Envir {maxidx=maxidx_new,tenv=Envir.term_env match_envir,tyenv=Envir.type_env match_envir})
    in SOME (envir_return,infer_instantiate ctxt (envlist ctxt match_envir) (Thm.incr_indexes (maxidx+1) hint_thm))
end handle _ => NONE (* s.a. *)

(* assembles list of matching hints from list, drops first i hints*)
fun appl_hints ctxt envir (t1,t2) i =
  map Option.valOf
    o drop i
    o filter Option.isSome
    o map (fn h => try_hint_unif ctxt envir (t1,t2) h)

(* discharges n prems by applying reflexivity *)
fun discharge_prems thm =
  fn 0 => thm | n => discharge_prems (thm OF [rel_refl]) (n-1)

(* instantiates thm DEADID.rel_refl with [t/x_0] *)
fun instantiate_rel_refl ctxt t =
  infer_instantiate ctxt [(("x",0),Thm.cterm_of ctxt t)] rel_refl

(* first order unification with hints *)
fun hint_unify ctxt hints (term1,term2) env =
let fun unif envir (t1,t2) =
  (case (t1,t2) of
      (Free(x,tyx),Free(y,tyy)) =>
        if x=y then (ty_unify ctxt (tyx,tyy) envir,instantiate_rel_refl ctxt (Free(x,tyx)))  else raise Unif ""
    | (Const(x,tyx),Const(y,tyy)) =>
        if x=y then (ty_unify ctxt (tyx,tyy) envir,instantiate_rel_refl ctxt (Const(x,tyx))) else raise Unif ""
    | (f $ t1,g $ t2) =>
        let val (envir',thm_fg) = unif envir (f,g)
            val (envir'',thm_xy) = unif envir' (Envir.norm_term envir' t1, Envir.norm_term envir' t2)
        in (envir'',cong OF [infer_instantiate ctxt (envlist ctxt envir'') thm_fg,infer_instantiate ctxt (envlist ctxt envir'') thm_xy]) end
    | (Var(x,tyx),Var(y,tyy)) =>
        let val new_env = ty_unify ctxt (tyx,tyy) envir
             val new_tenv = Envir.type_env new_env in
         (if x=y then ty_unify ctxt (tyx,tyy) envir
                 else Envir.update ((x,Envir.norm_type new_tenv tyx),Var(y,Envir.norm_type new_tenv tyy)) new_env,
          instantiate_rel_refl ctxt (Var(y,Envir.norm_type new_tenv tyy))) end
    | (Var(x,tyx),t) =>
        if Term.is_open t then raise Unif ""
         else if contains_var x t then raise Unif "(Occurs Check)" else
          (case Envir.lookup envir (x,tyx) of
              NONE    => let val new_env = ty_unify ctxt (tyx,fastype_of t) envir in 
                          (Envir.update ((x,Envir.norm_type (Envir.type_env new_env) tyx),t) new_env,instantiate_rel_refl ctxt t) end
            | SOME t' => if Envir.aeconv (t',t) then (envir,instantiate_rel_refl ctxt t) else unif envir (t',t))
    | (t,Var(x,tyx))                => unif envir (Var(x,tyx),t)
    | (Abs(_,ty1,t1),Abs(_,ty2,t2)) => unif (ty_unify ctxt (ty1,ty2) envir) (t1,t2)
    | (Bound i,Bound j)            => if i=j then (envir,instantiate_rel_refl ctxt (Bound i)) else raise Unif ""
    | (t1,Abs(_,_,t2))              => unif envir (t2,(incr t1)$(Bound 0))
    | (Abs(_,_,t1),t2)              => unif envir (t1,(incr t2)$(Bound 0))
    | _ => raise Unif "")
   handle Unif _ =>
     let val hintlist = (appl_hints ctxt envir (Envir.norm_term envir t1,Envir.norm_term envir t2) 0 hints)
     in hd hintlist handle Empty => raise Unif ("Hint Unification failed") end
in
  let val (sigma,thm) = unif
    (Envir.Envir {tenv=Envir.term_env env,tyenv=Envir.type_env env,maxidx=Int.max (maxidx_of_term term1,maxidx_of_term term2)})
    (term1 |> Envir.norm_term env |> Envir.eta_contract,
     term2 |> Envir.norm_term env |> Envir.eta_contract)
  in (sigma, discharge_prems thm (Thm.nprems_of thm)) end
end

fun first_order_unify_h ctxt =
  hint_unify ctxt (gen_hint_list ctxt)

end