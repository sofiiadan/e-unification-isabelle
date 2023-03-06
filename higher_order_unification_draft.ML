(*  Title:      E_Unification/higher_order_unification_draft.ML
    Author:     Kevin Kappelmann, Paul Bachmann, Sofiia Danylchenko

Adapt the Pure/unify.ML to e-unification functionality.
*)

signature HIGHER_ORDER_UNIFICATION_DRAFT =
sig
  structure Logger : LOGGER

  val unify :  Unification_Base.unifier
  val hounify: Unification_Base.unifier
end

structure Higher_Order_Unification : HIGHER_ORDER_UNIFICATION_DRAFT =
struct

(* shared utils *)

structure Logger = @{new_logger "higher_order_unification_draft"}

structure Util = Unification_Util

(*TODO: 
  1) one way to transform flexflex pairs: 
    1.1)smash them - +
    1.2)apply new env to input terms - + 
    1.3)get thm - +
  2) fix return types - +
  3) example testing - +? (we can as well use the tests for higher_order_unification)
  4) check out Thm module for flexflex pairs - + 
  5) create a latex file \<and> write what unif_resolve does - +- 
*)
(*use env, apply it to t1,t2 \<and> resolve t1,t2 with "?x = ?x" - implemented  \<rightarrow> higher_order_unification.ML*)

(*standard unification*)
fun unify ctxt tp env =  
  let 
    fun unif () = 
      let                                      
        val unifiers =  Unify.unifiers (Context.Proof ctxt, env, [tp])
        val new_envs = 
          let
            fun map_flexflex_to_env (env,tus) = Unify.smash_unifiers (Context.Proof ctxt) tus env  
          in
            Seq.map map_flexflex_to_env unifiers |> Seq.flat
          end
        val get_thms_from_input = 
          let
            fun create_eq_thm (t1,t2) = 
              let
                val new_env = Seq.hd new_envs
                val thm = Logic.mk_equals (Envir.norm_term new_env t1, Envir.norm_term new_env t2) 
                  |> Thm.cterm_of @{context} (*?*)
                  |> Thm.reflexive
              in
                pair new_env thm
              end
        in
          Seq.map create_eq_thm (Seq.of_list [tp])
        end
    in
      get_thms_from_input
    end
    handle Unification_Base.UNIF =>
      let
        val tp' = apply2 (Util.norm_term_unif env) tp
        val _ = @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
            Pretty.str "Higher-order unification (smash flexflex pairs version) failed (type mismatch) ",
            Util.pretty_unif ctxt tp'
          ]
          |> Pretty.string_of)
      in Seq.empty end
   in
    (@{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.block [
        Pretty.str "Higher-order unifying (smash flexflex pairs version) ",
        Util.pretty_unif ctxt (apply2 (Envir.norm_term env) tp)
      ]                         
      |> Pretty.string_of);
    unif ())
   end

(*higher-order unification*)
fun hounify ctxt tp env =  
  let 
    fun unif () = 
      let                                      
        val unifiers =  Unify.unifiers (Context.Proof ctxt, env, [tp])
        val new_envs = 
          let
            fun map_flexflex_to_env (env,tus) = Unify.smash_unifiers (Context.Proof ctxt) tus env  
          in
            Seq.map map_flexflex_to_env unifiers |> Seq.flat
          end
        val get_thms_from_input = 
          let
            fun create_eq_thm (t1,t2) = 
              let
                val new_env = Seq.hd new_envs
                val thm = Logic.mk_equals (Envir.norm_term new_env t1, Envir.norm_term new_env t2) 
                  |> Thm.cterm_of @{context} (*?*)
                  |> Thm.reflexive
              in
                pair new_env thm
              end
        in
          Seq.map create_eq_thm (Seq.of_list [tp])
        end
    in
      get_thms_from_input
    end
    handle Unification_Base.UNIF =>
      let
        val tp' = apply2 (Util.norm_term_unif env) tp
        val _ = @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
            Pretty.str "Higher-order hounification (smash flexflex pairs version) failed (type mismatch) ",
            Util.pretty_unif ctxt tp'
          ]
          |> Pretty.string_of)
      in Seq.empty end
   in
    (@{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.block [
        Pretty.str "Higher-order hounifying (smash flexflex pairs version) ",
        Util.pretty_unif ctxt (apply2 (Envir.norm_term env) tp)
      ]                         
      |> Pretty.string_of);
    unif ())
   end

end

