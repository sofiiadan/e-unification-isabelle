\<^marker>\<open>contributor "Sofiia Danylchenko"\<close>
theory unification_tactics
imports
  Complex_Main
  E_Unification.E_Unification
begin
(*TODO: 
1.tactic check if equality
2.fail as convention requires
3.left side, right side => pass to unifier
=> seq of results (env*thm) return thm 
else handle the exeption and fails in a good way

 Write a function that takes two terms and
    a. Calls the first-order unifier to unify the terms
    b. If the terms do not unify, prints a debugging message and then throws the exception UNIF
    c. If the terms unify, returns the normalised theorem and prints the result.
*)


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
            |> Pretty.string_of) (*Question: how to specify?*) 
          in
            raise Unification_Base.UNIF    
          end
         | SOME ((env,thm),t2) => 
      let
        val log = Util.log_unif_result ctxt (p,q) (env,thm) (*unified stuff to proven theorem*)
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
- update the goal (apply the new env to the initially passed problem)
- remove subproblem n from updated problem ("solve it") with (env,thm)
- return newly adjusted problem thm'
- 3 final steps are done for all env from seq of (env,thm) (use functions on seq for iteration)
(Seq.map 3 steps seq of (env,thm) \<rightarrow> seq thm)
// a\<rightarrow>b ... \<rightarrow> goal
beware of TrueProp \<and> remove it
*)

ML\<open>
(*?: where can I look up this how to get terms out of P \<equiv> Q*)
fun get_terms thm = 
  let 
    val term = @{term "P \<equiv> Q"}
  in
    case Thm.full_prop_of thm of
      term => undefined
      | _ => undefined
  end

fun unif_tactic n thm =
  let
   val subproblem = thm (*?: should be subproblem n from thm*)
  in
    let
      val goal = SOMEGOAL n subproblem (*?: how to get tactics, not thm \<rightarrow> thm Seq? Use PRIMITIVE or? *)
      val unify_terms = undefined (*unification like unify_first_order*) 
    in
      Seq.map unify_terms goal
    end
  end
\<close>


ML\<open>\<close>
ML\<open>\<close>
end