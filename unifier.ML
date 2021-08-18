(*  Title:      Unification_Hints/unifiers.ML
    Author:     Kevin Kappelmann

Shared type definitions for unifiers.
*)

signature UNIFIER_TYPES =
sig
  type unifier = Context.generic -> term * term -> Envir.env -> (Envir.env * thm)
end

structure Unifier_Types : UNIFIER_TYPES =
struct

type unifier = Context.generic -> term * term -> Envir.env -> (Envir.env * thm)

end