(*  Title:      E_Unification/higher_order_unification.ML
    Author:     Kevin Kappelmann, Paul Bachmann, Sofiia Danylchenko

Higher-order E-unification.
*)

signature HIGHER_ORDER_UNIFICATION =
sig
  structure Logger : LOGGER

  val unify : Context.generic * Envir.env * ((term * term) list) ->
    (Envir.env * thm) Seq.seq
  val hounify: Context.generic * Envir.env * ((term * term) list) ->
    (Envir.env * thm) Seq.seq (*change return types*)
end

structure Higher_Order_Unification : HIGHER_ORDER_UNIFICATION =
struct

(* shared utils *)

structure Logger = @{new_logger "higher_order_unification"}

structure Util = Unification_Util

(*create equality thm from term*term \<and> env*)
fun eq_thm ctxt env (t1,t2) = Logic.mk_equals (Envir.norm_term env t1, Envir.norm_term env t2) 
  |> Thm.cterm_of ctxt 
  |> Thm.reflexive (*?: should the theorem itself be normalized*)

(*TODO:
- ?: add term*term list to term (cterm) conversion? What does it mean for flexflex pairs? 
- env to (term*term \<rightarrow> term) \<rightarrow> (term list \<rightarrow> term) \<rightarrow> thm 
*)  

(*Create a thm applying env to term*term list that terms are equal, 
(Envir.env * (term * term) list) Seq.seq -> to have a (Envir.env * thm) Seq.seq)*)
fun create_thm ctxt env fflist = 
  case fflist of
   (t1,t2)::_ => eq_thm ctxt env (t1,t2)
   | [] =>  raise ERROR "empty list of flexflex pairs"

fun map_unifiers unifiers = 
  let
   fun map_flexflex_to_thm (env, fflist) = (env, create_thm @{context} env fflist) (*?: how to deal with ctxt?*)
  in
    Seq.map map_flexflex_to_thm unifiers
  end

(*standard unification*)
fun unify (cxtx, env, fflist) =  Unify.unifiers (cxtx, env, fflist) |> map_unifiers

(*higher-order unification*)
fun hounify (cxtx, env, fflist) =  Unify.hounifiers (cxtx, env, fflist) |> map_unifiers

end

