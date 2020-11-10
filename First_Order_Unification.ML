(*First Order Unification*)
signature First_Order_Unification = 
sig
  exception Unif of string
  exception MalformedHint of string
  val first_order_unify :
    Proof.context -> term * term -> Envir.env -> Envir.env
  type hint = (term * term) * Envir.tenv * thm
  val genHintList : Proof.context -> hint list
  val hint_unify :
    Proof.context -> hint list ->  term * term -> Envir.env -> Envir.env
  val first_order_unify_h :
    Proof.context -> term * term -> Envir.env -> Envir.env
  

end;
(*
fun mapUpdate x t' = fn
    Var (y,tyy) => if y=x then t' else Var (y,tyy)
  | Abs (s,T,t) => Abs (s,T,mapUpdate x t' t)
  | t1 $ t2     => mapUpdate x t' t1 $ mapUpdate x t' t2
  | t => t;

fun upd_subterms (Envir.Envir {maxidx,tenv,tyenv}) x t' =
   Envir.Envir {maxidx = maxidx, tenv = Vartab.map (K (fn (tyt,t) => (tyt,mapUpdate x t' t))) tenv, tyenv = tyenv}
*)

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
fun incr_max max = mapbnd (fn i => i+max+1)

(*Occurs check for first_order_unify*)
fun containsV v =
  fn Var (x,_)   => x = v
  |  t1 $ t2     => containsV v t2 orelse containsV v t1
  |  Abs (_,_,t) => containsV v t
  |  _           => false

fun first_order_unify ctxt (term1,term2) env =
let fun ty_unify typs (Envir.Envir {maxidx,tenv,tyenv}) =
      let val (new_tyE,_) = Sign.typ_unify (Proof_Context.theory_of ctxt) typs (tyenv,0)
      in Envir.Envir {maxidx = maxidx, tenv = tenv, tyenv = new_tyE} end
in let fun unif envir =
  fn (Free(x,tyx),Free(y,tyy)) =>
       if x=y then ty_unify (tyx,tyy) envir else raise Unif ""
  |  (Const(x,tyx),Const(y,tyy)) =>
       if x=y then ty_unify (tyx,tyy) envir else raise Unif ""
  |  (f $ t1,g $ t2) =>
       let val envir' = unif envir (f,g) in
       unif envir' (Envir.norm_term envir' t1, Envir.norm_term envir' t2) end (*norm weglassen \<Longrightarrow> Zirkuläre Mappings!*)
  |  (Var(x,tyx),Var(y,tyy)) =>
       if x=y then ty_unify (tyx,tyy) envir
              else let val new_env = ty_unify (tyx,tyy) envir in
                Envir.update ((x,Envir.norm_type (Envir.type_env new_env) tyx),Var(y,Envir.norm_type (Envir.type_env new_env) tyy)) new_env end (*statt tyx type lookup in envir*)
  |  (Var(x,tyx),t) =>
       if Term.is_open t then raise Unif ""
        else if containsV x t then raise Unif "(Occurs Check) " else
         (case Envir.lookup envir (x,tyx) of
             NONE    => let val new_env = ty_unify (tyx,fastype_of t) envir in 
                         Envir.update ((x,Envir.norm_type (Envir.type_env new_env) tyx),t) new_env end
           | SOME t' => if Envir.aeconv (t',t) then envir else unif envir (t',t))
  |  (t,Var(x,tyx))                => unif envir (Var(x,tyx),t)
  |  (Abs(_,ty1,t1),Abs(_,ty2,t2)) => unif (ty_unify (ty1,ty2) envir) (t1,t2)
  |  (Bound i, Bound j)            => if i=j then envir else raise Unif ""
  |  (t1,Abs(_,_,t2))              => unif envir (t2,(incr t1)$(Bound 0))
  |  (Abs(_,_,t1),t2)              => unif envir (t1,(incr t2)$(Bound 0))
  |  _ => raise Unif ""
  in unif env (Envir.norm_term env term1,Envir.norm_term env term2) handle _ => raise Unif "Exception raised" end
end

(* increase index of all Vars in term by maxidx+1 *)
fun incr_idx maxidx =
   fn Var ((name,idx),typ) => Var ((name,idx+maxidx+1),typ)
   |  Abs (s,T,t) => (Abs(s,T,incr_idx maxidx t))
   |  t1 $ t2 => incr_idx maxidx t1 $ incr_idx maxidx t2
   |  t => t

fun unzip l =
  case l of [] => ([],[])
    | (x,y)::xys => let val (xs,ys) = unzip xys in (x::xs,y::ys) end

fun valsOfSomeList l = filter Option.isSome l |> map Option.valOf

fun genHint thm = (SOME
  (thm |> Thm.concl_of
       |> (fn Const ("HOL.Trueprop",_) $ (Const ("HOL.eq",_) $ t1 $ t2) => (t1,t2)),
  (thm |> Thm.prems_of
       |> map (fn (Const ("HOL.Trueprop", _) $ (Const ("HOL.eq",_) $ Var (vn,typ) $ t)) => (vn,(typ,t)))
       |> fold (fn tup => fn env => Vartab.update_new tup env)) Vartab.empty, thm),"")
  handle Match => (NONE,Thm.derivation_name thm)

fun strings_flat (x::xs) = fold (fn curr => fn acc => acc^", "^curr) xs x

(* generates a list of hints from named theorems "hints" *)
fun genHintList ctxt =
  let val (hs,strs) = Proof_Context.get_thms ctxt "hints" |> map genHint |> unzip
      val thmStrs = filter (fn x => x <> "") strs
      val _ = if thmStrs = [] then ()
        else tracing ("The following theorems cannot be used as hints: "^ strings_flat thmStrs)
  in valsOfSomeList hs end

fun ienvs_Envir i (ty,te) = Envir.Envir {tyenv=ty,tenv=te,maxidx=i}

fun envTup (Envir.Envir {tyenv,tenv,...}) = (tyenv,tenv)

fun hint_unify ctxt hints (term1,term2) env =
let fun ty_unify typs (Envir.Envir {maxidx,tenv,tyenv}) =
      let val (new_tyE,_) = Sign.typ_unify (Proof_Context.theory_of ctxt) typs (tyenv,maxidx)
      in Envir.Envir {maxidx = maxidx, tenv = tenv, tyenv = new_tyE} end
    fun try_hint (unifEnvir as Envir.Envir {maxidx,...}) (t1,t2) ((h1_raw,h2_raw),tenv,thm) =
      let val unifEnvs = envTup unifEnvir
          val pmatch = Pattern.match (Proof_Context.theory_of ctxt)
          val (h1,h2) = (incr_idx maxidx h1_raw,incr_idx maxidx h2_raw)
          val maxidx_new = Int.max (maxidx,Int.max (maxidx_of_term h1,maxidx_of_term h2))
          val matchEnvir =
              (pmatch (h2,t2) (pmatch (h1,t1) unifEnvs)
              handle Pattern.MATCH => pmatch (h2,t1) (pmatch (h1,t2) unifEnvs))
              |> ienvs_Envir maxidx_new
          fun foldfun ((s,i),(typ,term)) envir =
              hint_unify ctxt hints (Envir.norm_term matchEnvir (incr_idx maxidx term),Envir.lookup matchEnvir ((s,i+maxidx+1),typ) |> Option.valOf) envir
          in
            SOME (Vartab.fold foldfun tenv (Envir.Envir {maxidx=maxidx_new,tenv=Envir.term_env unifEnvir,tyenv=Envir.type_env unifEnvir}))
          end
    fun appl_hints envir (t1,t2) i hs =
      hs |> map (fn h => try_hint envir (t1,t2) h handle Pattern.MATCH => NONE)
         |> filter Option.isSome
         |> drop i
         |> map Option.valOf
in let fun unif envir (t1,t2) =
  (case (t1,t2) of
      (Free(x,tyx),Free(y,tyy)) =>
        if x=y then ty_unify (tyx,tyy) envir else raise Unif ""
    | (Const(x,tyx),Const(y,tyy)) =>
        if x=y then ty_unify (tyx,tyy) envir else raise Unif ""
    | (f $ t1,g $ t2) =>
        let val envir' = unif envir (f,g) in
        unif envir' (Envir.norm_term envir' t1, Envir.norm_term envir' t2) end (*norm weglassen \<Longrightarrow> Zirkuläre Mappings!*)
    | (Var(x,tyx),Var(y,tyy)) =>
        if x=y then ty_unify (tyx,tyy) envir
               else let val new_env = ty_unify (tyx,tyy) envir in
                Envir.update ((x,Envir.norm_type (Envir.type_env new_env) tyx),Var(y,Envir.norm_type (Envir.type_env new_env) tyy)) new_env end
    | (Var(x,tyx),t) =>
        if Term.is_open t then raise Unif ""
         else if containsV x t then raise Unif "(Occurs Check)" else
          (case Envir.lookup envir (x,tyx) of
              NONE    => let val new_env = ty_unify (tyx,fastype_of t) envir in 
                          Envir.update ((x,Envir.norm_type (Envir.type_env new_env) tyx),t) new_env end
            | SOME t' => if Envir.aeconv (t',t) then envir else unif envir (t',t))(*
    | (t,Var(x,tyx))                =>
        if Term.is_open t then raise Unif ""
         else if containsV x t then raise Unif "(Occurs Check)" else
          (case Envir.lookup envir (x,tyx) of
              NONE    => let val new_env = ty_unify (tyx,fastype_of t) envir in
                          Envir.update ((x,Envir.norm_type (Envir.type_env new_env) tyx),t) new_env end
            | SOME t' => if Envir.aeconv (t,t') then envir else unif envir (t,t'))*)
    | (t,Var(x,tyx))                => unif envir (Var(x,tyx),t)
    | (Abs(_,ty1,t1),Abs(_,ty2,t2)) => unif (ty_unify (ty1,ty2) envir) (t1,t2)
    | (Bound i, Bound j)            => if i=j then envir else raise Unif ""
    | (t1,Abs(_,_,t2))              => unif envir (t2,(incr t1)$(Bound 0))
    | (Abs(_,_,t1),t2)              => unif envir (t1,(incr t2)$(Bound 0))
    | _ => raise Unif "")
   handle Unif _ => 
     let val hintlist = (appl_hints envir (Envir.norm_term envir t1,Envir.norm_term envir t2) 0 hints)
     in hd hintlist handle Empty => raise Unif ("Hint Unification failed ") end
  in
    unif (Envir.Envir {tenv=Envir.term_env env,tyenv=Envir.type_env env,maxidx=3}) (Envir.norm_term env term1,Envir.norm_term env term2)
  end
end

fun first_order_unify_h ctxt =
  hint_unify ctxt (genHintList ctxt)


end