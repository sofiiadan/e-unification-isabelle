\<^marker>\<open>contributor "Sofiia Danylchenko"\<close>
theory unification_tactics
imports
  Complex_Main
  E_Unification.E_Unification
begin

ML\<open>
  val x = ()
  structure Util = Unification_Util
  structure Logger = @{new_logger "unification_tactics"}
\<close>

ML\<open> 
 fun unify_first_order ctxt (p,q) env = 
   let
      val unified =  First_Order_Unification.unify ctxt (p, q) env 
        |> Seq.pull 
    in
      case unified of
         NONE => 
        let 
          val log = @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
              Pretty.str "Exception message ",
              Util.pretty_unif ctxt (p, q)]
            |> Pretty.string_of) 
          in
            raise Unification_Base.UNIF    
          end
         | SOME ((env,thm),t2) => 
      let
        val log = Util.log_unif_result ctxt (p,q) (env,thm)
      in
        Util.norm_thm Util.norm_type_unif Util.norm_term_unif ctxt env thm
      end
    end
\<close>


(*
- tactic takes integer n to specify a subproblem \<and> it takes a problem thm - +
- extract subproblem n from passed thm - +
- extract the goal from the subproblem extracted - +
- extract p,q if the goal form is P \<equiv> Q - +
- call unifier on p,q \<Rightarrow> get the seq of (env, thm) - +
- update the goal (apply the new env to the initially passed problem) - +
- remove subproblem n from updated problem ("solve it") with (env,thm) - +
- return newly adjusted problem thm' - +
- 3 final steps are done for all env from seq of (env,thm) (use functions on seq for iteration) - +
(Seq.map 3 steps seq of (env,thm) \<rightarrow> seq thm)
// a\<rightarrow>b ... \<rightarrow> goal
beware of TrueProp \<and> remove it

?: resolve current errors
*)

ML\<open>
(*Kevin: Thm.dest_equals; example:*)
val (lhs, rhs) = Thm.dest_equals @{cterm "P \<equiv> Q"}
(*Kevin: similarly, there is dest_Trueprop to destruct a Trueprop*)
val p = HOLogic.dest_Trueprop @{prop "\<forall>x. x = x"}
(*?: where can I look up this how to get terms out of P \<equiv> Q*)

(*extract p,q if the goal form is P \<equiv> Q*)
fun terms thm = 
             let
               val p = Thm.dest_equals_lhs thm
               val q = Thm.dest_equals_rhs thm
             in
               (Thm.term_of p,Thm.term_of q)
             end


(* 3 final steps are done for all env from seq of (env,thm)*)
fun resolve_goal ctxt unified_goal thm = 
  let 
    fun update_goal ctxt unified_goal thm = case Seq.pull unified_goal of
        NONE => thm
 (*handle proper error message*)
       | SOME (env,thm') => 
          let
            (*update the goal (use env on thm)*)
            val updated_goal =  Util.norm_thm Util.norm_type_unif Util.norm_term_unif ctxt env thm
            (*remove subproblem n from updated problem ("solve it") with (env,thm)*)
            (*return newly adjusted problem thm'*)
            val remove_subproblem = Util.norm_thm Util.norm_type_unif Util.norm_term_unif ctxt env thm 
                  |> Thm.implies_elim updated_goal 
          in
            remove_subproblem
          end
  in
    Seq.map update_goal unified_goal
  end

fun unif_tac ctxt =
  let
    (* val subproblem = t *)
    (*Kevin: subgoal term is given in t, subogal index by i*)
    fun unif_subgoal (t, i) thm =
      let
        (*3. extract the goal from the subproblem extracted*)
        val goal = Thm.cterm_of ctxt t |> Thm.dest_equals_rhs (*implementation.pdf page 101?*)
        val (p,q) = terms thm
        val _ = @{log} ctxt (fn _ =>
            Pretty.block [
              Pretty.str ("Calling unification tactic on subgoal " ^ Int.toString i ^ ": "),
              Util.pretty_terms ctxt [p,q]
            ]
            |> Pretty.string_of
          )
        (*Kevin: I do not understand; type tactic = thm -> thm Seq.seq*)
        (*you now need to implement above tasks, starting from
          - extract the goal from the subproblem extracted
          The subgoal is t, but it might be of the form "A1 ==> A2 ... ==> C"
          and you now want to analyse whether C is indeed an equality
        *)
         (*4: extract p,q if the goal form is P \<equiv> Q *)
         val (p,q) = terms goal
         (*5: update the goal (apply the new env to the initially passed problem*)
         val env = Envir.empty 0
         val unify_terms = First_Order_Unification.unify ctxt (p,q) env
         fun resolve_goal' unified_seq thm  = 
             let 
                val pull_next = Seq.pull unified_seq
                fun update_goal unified_goal = case pull_next of
                    NONE => thm (*?: handle proper error message*)
                   | SOME (env,thm') => 
                      let
                        (*6. update the goal (use env on thm)*)
                        val updated_goal =  Util.norm_thm Util.norm_type_unif Util.norm_term_unif ctxt env thm
                        (*7. remove subproblem n from updated problem ("solve it") with (env,thm)*)
                        (*8. return newly adjusted problem thm'*)
                        val remove_subproblem = Util.norm_thm Util.norm_type_unif Util.norm_term_unif ctxt env thm 
                            |> Thm.implies_elim updated_goal  (*TODO*)
                      in
                         remove_subproblem 
                      end
              in
               (* 3 final steps are done for all env from seq of (env,thm)*)
               Seq.map update_goal unified_seq
              end
          val solved_goal = resolve_goal' unify_terms thm
      in Seq.single solved_goal end (*change that*)
  (*1-2. SUBGOAL extracts ith subgoal*)
  in SUBGOAL unif_subgoal end
\<close>

(*Here you can debug your code*)
schematic_goal example: "f x \<equiv> ?Y"
  apply (tactic \<open>unif_tac @{context} 1\<close>)
sorry


ML\<open>\<close>
ML\<open>\<close>
end