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

ML\<open>
  structure L = Logic

  val dummy = Term.dummyT

  val first_order_unifier = First_Order_Unification.unify

  fun unif_tac unifier ctxt  =
    let
      (* val subproblem = t *)
      fun unif_subgoal (t, i) thm =
        let
          (*3. extract the goal from the subproblem extracted*)
          (*take care of trueprop \<and> exception*)
          val concl = Logic.strip_imp_concl t (*implementation.pdf page 101?*)
          (*4: extract p,q if the goal form is P \<equiv> Q *)
          val (p,q) = Logic.dest_equals  concl
          val _ = @{log} ctxt (fn _ =>
            Pretty.block [
              Pretty.str ("Calling unification tactic on subgoal " ^ Int.toString i ^ ": "),
              Util.pretty_terms ctxt [p,q]
            ]
            |> Pretty.string_of
           )
           (*5: update the goal (apply the new env to the initially passed problem*)
           val env = Util.empty_envir (p,q)
           val unif_sq = unifier ctxt (p,q) env
           fun update_thm (env,eq_thm) = 
             let
                (*6. update the goal (use env on thm)*)
                val updated_thm =  Util.norm_thm Util.norm_type_unif Util.norm_term_unif ctxt env thm
                (*7. remove subproblem n from updated problem ("solve it") with (env,thm)*)
                (*8. return newly adjusted problem thm'*)
                val updated_sq = resolve0_tac [eq_thm] i updated_thm 
              in
                updated_sq
              end 
      (* 3 final steps are done for all env from seq of (env,thm)*)
      in Seq.map update_thm unif_sq |> Seq.flat end (*change that*)
    (*1-2. SUBGOAL extracts ith subgoal*)
    in SUBGOAL unif_subgoal end
\<close>

declare [[show_types = true]]

config [First_Order_Unification.Logger.log_level = Logger.DEBUG]

(*Here you can debug your code*)
schematic_goal example: "(f :: ?'c \<Rightarrow> 'b) x \<equiv> (?Y :: 'a \<Rightarrow>'b) ?Z"
  apply (tactic \<open>unif_tac first_order_unifier @{context} 1\<close>)
done

(*
1. Clean the function (indentations, remove old functions, etc.) - +-, add exceptions
2. Change it such that it takes a unifier as a parameter (types in Unification_Base.unifier) - +
3. Store a unifier as a context data:
    a. Read Implentation Manual 1.1.4 Context data
    b. Then implement context data that stores a unifier
    c. Test it: add a unifier, retrieve it, update it, etc.
4. Create a function that first retrieves the unifier from the context and then passes it to the unification tactic as a parameter
*)

ML\<open>\<close>
ML\<open>\<close>
end