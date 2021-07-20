(*  Title:      Pure/pattern.ML
    Author:     Tobias Nipkow, Christine Heinzelmann, and Stefan Berghofer, TU Muenchen

Unification of Higher-Order Patterns.

See also:
Tobias Nipkow. Functional Unification of Higher-Order Patterns.
In Proceedings of the 8th IEEE Symposium Logic in Computer Science, 1993.

TODO: optimize red by special-casing it
*)

signature PATTERNH =
sig
  exception Unif
  exception Pattern
  val unify_trace_failure: bool Config.T
  val unify_types: Context.generic -> typ * typ -> Envir.env -> Envir.env
  val h_unify: Context.generic -> term * term -> Envir.env -> Envir.env * thm
  val unify_abstraction: Context.generic -> thm -> term -> Envir.env -> thm
end;

structure PatternH: PATTERNH =
struct

exception Unif;
exception Pattern;

val unify_trace_failure = Config.declare_bool ("unify_trace_failure", \<^here>) (K false);

fun string_of_term ctxt env binders t =
  Syntax.string_of_term ctxt (Envir.norm_term env (subst_bounds (map Free binders, t)));

(*theorems reflexity, combination and symmetry*)
val reflexive = @{thm Pure.reflexive}
val combination = Thm.axiom @{theory} "Pure.combination"
val symmetric = @{thm Pure.symmetric}
val abstraction = Thm.axiom @{theory} "Pure.abstract_rule";

(*new helper funs from First_Order_Unification.ML*)

(*instantiates the first type variable in th with typ*)
fun instantiate_type_var ctxt typ thm =
  Thm.instantiate ([(hd (Term.add_tvars (Thm.full_prop_of thm) []), Thm.ctyp_of ctxt typ)], []) thm

(*instantiates Pure.reflexive with [t/x_0]*)
fun inst_refl ctxt t =
  let val pctxt = Context.proof_of ctxt
      val renamed_refl = instantiate_type_var pctxt (type_of t) reflexive
      val var =  (hd (Term.add_vars (Thm.full_prop_of renamed_refl) []))
      val ct = Thm.cterm_of pctxt t
  in infer_instantiate_types pctxt [(var,ct)] renamed_refl end

(*converts Envir into lists of var to cterm and tvar to ctype mappings*)
fun env_lists (Envir.Envir {tenv,tyenv,...}) ctxt =
  (map (fn (xi,(S,T)) => ((xi,S),Thm.ctyp_of ctxt T)) (Vartab.dest tyenv),
   map (fn (xi,(T,t)) => ((xi,T),Thm.cterm_of ctxt t)) (Vartab.dest tenv))

(*converts Envir into var to cterm list without type (for infer_instantiate)*)
fun envir_to_ct_map ctxt env = env_lists env ctxt |> snd |> map (fn ((a,_),c) => (a,c))

(*applies Envir substitutions to thm*)
fun norm_thm ctxt envir thm =
  let val pctxt = Context.proof_of ctxt in
    infer_instantiate pctxt (envir_to_ct_map pctxt envir) thm
  end

(*unifies the abstraction theorem with a theorem for a given var*)
fun unify_abstraction ctxt thm var env =
  let
    val pctxt = Context.proof_of ctxt
    val abstr = Thm.incr_indexes (Envir.maxidx_of env+1) abstraction
    val abstr_prem_t = Thm.prems_of abstr |> hd
    val thm_forall = forall_intr_list [Thm.cterm_of pctxt var] thm
    val thm_forall_t = Thm.concl_of thm_forall
    val unif_env = Pattern.unify ctxt (abstr_prem_t,thm_forall_t) env
    val _ = pretty_env pctxt (Envir.term_env unif_env)
    val inst_list = map
      (fn (idxn,(_,t)) => (idxn,Thm.cterm_of pctxt (Envir.norm_term unif_env t)))
      (Envir.term_env unif_env |> Vartab.dest)
    val abstr_inst = Drule.infer_instantiate pctxt inst_list abstr
  in
    abstr_inst OF [thm]
  end;

fun make_bvar i typ env =
  Var (("b",i),Envir.norm_type (Envir.type_env env) typ)

fun incr_maxidx i (Envir.Envir {tenv,tyenv,maxidx}) =
  Envir.Envir {tenv=tenv,tyenv=tyenv,maxidx=maxidx+i}

fun lookup_var bvars i =
  case List.find ((fn j => j=i) o fst) bvars of
    NONE => raise Unif
    | SOME (_,var) => var

val incr_bvars = map (fn (i,var)=>(i+1,var))

fun add_bvar typ env bvars = 
  let val bvar = make_bvar (Envir.maxidx_of env+1) typ env
  in (bvar,(0,bvar)::(incr_bvars bvars)) end

(*--- from here on helper funs from Pattern.ML ---*)

fun bname binders i = fst (nth binders i);
fun bnames binders is = space_implode " " (map (bname binders) is);

fun typ_clash context (tye,T,U) =
  if Config.get_generic context unify_trace_failure then
    let
      val ctxt = Context.proof_of context;
      val t = Syntax.string_of_typ ctxt (Envir.norm_type tye T);
      val u = Syntax.string_of_typ ctxt (Envir.norm_type tye U);
    in tracing ("The following types do not unify:\n" ^ t ^ "\n" ^ u) end
  else ();

fun clash context a b =
  if Config.get_generic context unify_trace_failure
  then tracing ("Clash: " ^ a ^ " =/= " ^ b) else ();

fun boundVar binders i =
  "bound variable " ^ bname binders i ^ " (depth " ^ string_of_int i ^ ")";

fun clashBB context binders i j =
  if Config.get_generic context unify_trace_failure
  then clash context (boundVar binders i) (boundVar binders j) else ();

fun clashB context binders i s =
  if Config.get_generic context unify_trace_failure
  then clash context (boundVar binders i) s else ();

fun proj_fail context (env,binders,F,_,is,t) =
  if Config.get_generic context unify_trace_failure then
    let
      val ctxt = Context.proof_of context
      val f = Term.string_of_vname F
      val xs = bnames binders is
      val u = string_of_term ctxt env binders t
      val ys = bnames binders (subtract (op =) is (loose_bnos t))
    in
      tracing ("Cannot unify variable " ^ f ^
        " (depending on bound variables " ^ xs ^ ")\nwith term " ^ u ^
        "\nTerm contains additional bound variable(s) " ^ ys)
    end
  else ();

fun ocheck_fail context (F,t,binders,env) =
  if Config.get_generic context unify_trace_failure then
    let
      val ctxt = Context.proof_of context
      val f = Term.string_of_vname F
      val u = string_of_term ctxt env binders t
    in tracing ("Variable " ^ f ^ " occurs in term\n" ^ u ^ "\nCannot unify!\n") end
  else ();

fun occurs(F,t,env) =
    let fun occ(Var (G, T))   = (case Envir.lookup env (G, T) of
                                 SOME(t) => occ t
                               | NONE    => F=G)
          | occ(t1$t2)      = occ t1 orelse occ t2
          | occ(Abs(_,_,t)) = occ t
          | occ _           = false
    in occ t end;


fun mapbnd f =
    let fun mpb d (Bound(i))     = if i < d then Bound(i) else Bound(f(i-d)+d)
          | mpb d (Abs(s,T,t))   = Abs(s,T,mpb(d+1) t)
          | mpb d ((u1 $ u2))    = (mpb d u1)$(mpb d u2)
          | mpb _ atom           = atom
    in mpb 0 end;

fun idx [] _     = raise Unif
  | idx(i::is) j = if (i:int) =j then length is else idx is j;

fun mkabs (binders,is,t)  =
    let fun mk(i::is) = let val (x,T) = nth binders i
                        in Abs(x,T,mk is) end
          | mk []     = t
    in mk is end;

val incr = mapbnd (fn i => i+1);

fun ints_of []             = []
  | ints_of (Bound i ::bs) =
      let val is = ints_of bs
      in if member (op =) is i then raise Pattern else i::is end
  | ints_of _              = raise Pattern;

fun ints_of' env ts = ints_of (map (Envir.head_norm env) ts);

fun app (s,(i::is)) = app (s$Bound(i),is)
  | app (s,[])      = s;

(* split_type ([T1,....,Tn]---> T,n,[]) = ([Tn,...,T1],T) *)
fun split_type (T,0,Ts)                    = (Ts,T)
  | split_type (Type ("fun",[T1,T2]),n,Ts) = split_type (T2,n-1,T1::Ts)
  | split_type _                           = raise Fail "split_type";

fun type_of_G env (T, n, is) =
  let
    val tyenv = Envir.type_env env;
    val (Ts, U) = split_type (Envir.norm_type tyenv T, n, []);
  in map (nth Ts) is ---> U end;

fun mk_hnf (binders,is,G,js) = mkabs (binders, is, app(G,js));

fun mk_new_hnf(env,binders,is,F as (a,_),T,js) =
  let val (env',G) = Envir.genvar a (env,type_of_G env (T,length is,js))
  in Envir.update ((F, T), mk_hnf (binders, is, G, js)) env' end;

(*predicate: downto0 (is, n) <=> is = [n, n - 1, ..., 0]*)
fun downto0 (i :: is, n) = i = n andalso downto0 (is, n - 1)
  | downto0 ([], n) = n = ~1;

(*mk_proj_list(is) = [ |is| - k | 1 <= k <= |is| and is[k] >= 0 ]*)
fun mk_proj_list is =
    let fun mk(i::is,j) = if is_some i then j :: mk(is,j-1) else mk(is,j-1)
          | mk([],_)    = []
    in mk(is,length is - 1) end;

fun proj(s,env,binders,is) =
    let fun trans d i = if i<d then i else (idx is (i-d))+d;
        fun pr(s,env,d,binders) = (case Envir.head_norm env s of
              Abs(a,T,t) => let val (t',env') = pr(t,env,d+1,((a,T)::binders))
                            in (Abs(a,T,t'),env') end
            | t => (case strip_comb t of
                (c as Const _,ts) =>
                         let val (ts',env') = prs(ts,env,d,binders)
                         in (list_comb(c,ts'),env') end
                 | (f as Free _,ts) =>
                         let val (ts',env') = prs(ts,env,d,binders)
                         in (list_comb(f,ts'),env') end
                 | (Bound(i),ts) =>
                         let val j = trans d i
                             val (ts',env') = prs(ts,env,d,binders)
                         in (list_comb(Bound j,ts'),env') end
                 | (Var(F as (a,_),Fty),ts) =>
                      let val js = ints_of' env ts;
                          val js' = map (try (trans d)) js;
                          val ks = mk_proj_list js';
                          val ls = map_filter I js'
                          val Hty = type_of_G env (Fty,length js,ks)
                          val (env',H) = Envir.genvar a (env,Hty)
                          val env'' =
                            Envir.update ((F, Fty), mk_hnf (binders, js, H, ks)) env'
                      in (app(H,ls),env'') end
                 | _  => raise Pattern))
        and prs(s::ss,env,d,binders) =
              let val (s',env1) = pr(s,env,d,binders)
                  val (ss',env2) = prs(ss,env1,d,binders)
              in (s'::ss',env2) end
          | prs([],env,_,_) = ([],env)
   in if downto0(is,length binders - 1) then (s,env)
      else pr(s,env,0,binders)
   end;

(* mk_ff_list(is,js) = [ length(is) - k | 1 <= k <= |is| and is[k] = js[k] ] *)
fun mk_ff_list(is,js) =
    let fun mk([],[],_)        = []
          | mk(i::is,j::js, k) = if (i:int) = j then k :: mk(is,js,k-1)
                                        else mk(is,js,k-1)
          | mk _               = raise Fail "mk_ff_list"
    in mk(is,js,length is-1) end;

fun flexflex1(env,binders,F,Fty,is,js) =
  if is=js then
    (env,inst_refl (Context.the_generic_context()) (Envir.norm_term env (app (Var(F,Fty),is))))
  else
    let val ks = mk_ff_list(is,js)
        val env' = mk_new_hnf(env,binders,is,F,Fty,ks)
    in (env',inst_refl (Context.the_generic_context()) (Envir.norm_term env' (app (Var(F,Fty),is))))
    end;

fun flexflex2(env,binders,F,Fty,is,G,Gty,js) =
  let fun ff(F,Fty,is,G as (a,_),Gty,js) =
        if subset (op =) (js, is)
        then
          let val t = mkabs(binders,is,app(Var(G,Gty),map (idx is) js))
              val env'' = Envir.update ((F, Fty), t) env
          in (env'',inst_refl (Context.the_generic_context()) (Envir.norm_term env'' (app(Var(G,Gty),map (idx is) js))))
          end
        else
          let val ks = inter (op =) js is
              val Hty = type_of_G env (Fty,length is,map (idx is) ks)
              val (env',H) = Envir.genvar a (env,Hty)
              fun lam is = mkabs(binders,is,app(H,map (idx is) ks))
              val env'' = Envir.update ((G, Gty), lam js) (Envir.update ((F, Fty), lam is) env')
          in (env'', inst_refl (Context.the_generic_context()) (Envir.norm_term env' (app(H,map (idx is) ks))))
          end;
  in if Term_Ord.indexname_ord (G,F) = LESS then ff(F,Fty,is,G,Gty,js) else ff(G,Gty,js,F,Fty,is)
  end;

fun unify_types context (T, U) (env as Envir.Envir {maxidx, tenv, tyenv}) =
  if T = U then env
  else
    let
      val thy = Context.theory_of context
      val (tyenv', maxidx') = Sign.typ_unify thy (U, T) (tyenv, maxidx)
    in Envir.Envir {maxidx = maxidx', tenv = tenv, tyenv = tyenv'} end
    handle Type.TUNIFY => (typ_clash context (tyenv, T, U); raise Unif);

fun unif hints context binders bvars (s,t) env = case (Envir.head_norm env s, Envir.head_norm env t) of
      (Abs(ns,Ts,ts),Abs(nt,Tt,tt)) =>
        let
          val name = if ns = "" then nt else ns
          val env' = unify_types context (Ts, Tt) env
          val (bvar,bvars') = add_bvar Ts env' bvars
          val (env'',thm) = unif hints context ((name,Ts)::binders) bvars' (ts,tt) (incr_maxidx 1 env')
        in (env'',unify_abstraction context thm (Envir.norm_term env'' bvar) env'') end
    | (Abs(ns,Ts,ts),t) =>
        let
          val (bvar,bvars') = add_bvar Ts env bvars
          val env' = incr_maxidx 1 env
          val (env',thm) = unif hints context ((ns,Ts)::binders) bvars' (ts,(incr t)$Bound(0)) env'
        in (env',unify_abstraction context thm bvar env') end
    | (t,Abs(nt,Tt,tt)) =>
        let
          val (bvar,bvars') = add_bvar Tt env bvars
          val env' = incr_maxidx 1 env
          val (env',thm) = unif hints context ((nt,Tt)::binders) bvars' ((incr t)$Bound(0),tt) env'
        in (env',unify_abstraction context thm bvar env') end
    | p => cases hints context (binders,bvars,env,p)

and cases hints context (binders,bvars,env,(s,t)) = (case (strip_comb s,strip_comb t) of
       ((Var(F,Fty),ss),(Var(G,Gty),ts)) =>
         if F = G then flexflex1(env,binders,F,Fty,ints_of' env ss,ints_of' env ts)
                  else flexflex2(env,binders,F,Fty,ints_of' env ss,G,Gty,ints_of' env ts)
      | ((Var(F,Fty),ss),_)           => flexrigid context (env,binders,F,Fty,ints_of' env ss,t)
      | (_,(Var(F,Fty),ts))           => flexrigid context (env,binders,F,Fty,ints_of' env ts,s)
      | ((Const c,ss),(Const d,ts))   => rigidrigid hints context (env,binders,bvars,true,c,d,ss,ts)
      | ((Free(f),ss),(Free(g),ts))   => rigidrigid hints context (env,binders,bvars,false,f,g,ss,ts)
      | ((Bound(i),ss),(Bound(j),ts)) => rigidrigidB hints context (env,binders,bvars,i,j,ss,ts)
      | ((Abs(_),_),_)                => raise Pattern
      | (_,(Abs(_),_))                => raise Pattern
      | ((Const(c,_),_),(Free(f,_),_)) => (clash context c f; raise Unif)
      | ((Const(c,_),_),(Bound i,_))   => (clashB context binders i c; raise Unif)
      | ((Free(f,_),_),(Const(c,_),_)) => (clash context f c; raise Unif)
      | ((Free(f,_),_),(Bound i,_))    => (clashB context binders i f; raise Unif)
      | ((Bound i,_),(Const(c,_),_))   => (clashB context binders i c; raise Unif)
      | ((Bound i,_),(Free(f,_),_))    => (clashB context binders i f; raise Unif))
  handle exn =>
    let 
      val hint_results = HUnif.try_hints context Pattern.match h_unify env (s,t) hints
    in
      if null hint_results then
      raise exn else hd hint_results
    end

(*unifies ss with ts, instantiates reflexivity for base of fold with t*)
and fold_env_thm hints context (env,binders,bvars,t,ss,ts)=
      fold
        (fn ts => fn (envir,thm) => let val (envir',thm') = unif hints context binders bvars ts envir
         in (envir',Thm.combination (norm_thm context envir' thm) (norm_thm context envir' thm')) end)
        (ss~~ts) (env,inst_refl context (Envir.norm_term env t))

and rigidrigid hints context (env,binders,bvars,is_const,(a,Ta),(b,Tb),ss,ts) =
      if a<>b then (clash context a b; raise Unif)
      else
        let
          val env' = unify_types context (Ta,Tb) env
          val t = if is_const then Const(a,Ta) else Free(a,Ta)
        in
          fold_env_thm hints context (env',binders,bvars,t,ss,ts)
        end

and rigidrigidB hints context (env,binders,bvars,i,j,ss,ts) =
     if i <> j then (clashBB context binders i j; raise Unif)
     else fold_env_thm hints context (env,binders,bvars,lookup_var bvars i,ss,ts)

and flexrigid context (params as (env,binders,F,Fty,is,t)) =
      if occurs(F,t,env) then (ocheck_fail context (F,t,binders,env); raise Unif)
      else
        let val (u,env') = proj(t,env,binders,is)
            val env'' = Envir.update ((F, Fty), mkabs (binders, is, u)) env'
        in (env'',inst_refl context (Envir.norm_term env' (Var(F,Fty)))) end
            handle Unif => (proj_fail context params; raise Unif)

and h_unify context =
  unif (HUnif.gen_hint_list (Context.proof_of context)) context [] [];



end;
