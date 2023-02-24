\<^marker>\<open>contributor "Sofiia Danylchenko"\<close>
theory unification_tactics
imports
  Complex_Main
  E_Unification.E_Unification
begin

ML\<open>
  (*reference to functions needed for testing etc*)
  structure L = Logic

  structure Util = Unification_Util
  structure Logger = @{new_logger "unification_tactics"}

  val first_order_unifier = First_Order_Unification.unify
  val higher_order_unifier = Higher_Order_Pattern_Unification.unify
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

ML \<open>
  structure Unifier = Generic_Data
  (
    type T = Unification_Base.unifier
        val empty = First_Order_Unification.unify
        fun merge (u1,u2) = u1
  )
\<close>

ML\<open>
  (*Some tests for unification context*)
  fun get_unif ctxt = Unifier.get ctxt
  fun add_unif_1 _  = higher_order_unifier |> Unifier.put
  fun add_unif_2 _ = first_order_unifier |> Unifier.put
  (*?: is there any practical way to define test with hardcoded cases? using setup etc*)
\<close>

ML\<open>

  fun all_tac thm = Seq.single thm

  fun unif_tac unifier ctxt  =
    let
      (* val subproblem = t *)
      fun unif_subgoal (t, i) thm =
        let
          (*3. extract the goal from the subproblem extracted*)
          (*take care of trueprop \<and> exception*)
          val concl = Logic.strip_imp_concl t
          (*4: extract p,q if the goal form is P \<equiv> Q *)
          val (p,q) = Logic.dest_equals  concl
            handle TERM _  => let
              val _ = @{log} ctxt (fn _ =>
                Pretty.block [
                  Pretty.str ("The conclusion is not equality: "),
                  Util.pretty_terms ctxt [concl]
                ]
                |> Pretty.string_of
              )
            in
              raise ERROR "failed tactic" 
            end
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
      in
        let 
          val unif_thm_sq = Seq.map update_thm unif_sq |> Seq.flat
          handle ERROR _ =>  Seq.single thm
        in
          unif_thm_sq
        end
      end
    (*1-2. SUBGOAL extracts ith subgoal*) 
    in SUBGOAL unif_subgoal end

  (*Function that first retrieves the unifier from the context and 
  then passes it to the unification tactic as a parameter*)
  fun call_tac_with_unif (ctxt : Proof.context) =  
  let
    val unifier = Context.Proof ctxt |> Unifier.get
  in
    unif_tac unifier ctxt
  end 
\<close>

declare [[show_types = true]]

config [First_Order_Unification.Logger.log_level = Logger.DEBUG]

(*Here you can debug your code*)
schematic_goal example: "(f :: 'c \<Rightarrow> 'b) x \<equiv> (?Y :: 'c \<Rightarrow>'b) ?Z"
 (* apply intro*)
  apply (tactic \<open>unif_tac first_order_unifier @{context} 1\<close>)
  done

thm TrueI [OF ]

ML\<open>\<close>
end