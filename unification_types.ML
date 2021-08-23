(*  Title:      Unification_Hints/unification_types.ML
    Author:     Kevin Kappelmann

Shared type definitions for unifiers.
*)

signature UNIFICATION_TYPES =
sig
  type unifier = Context.generic -> term * term -> Envir.env -> (Envir.env * thm)
end

structure Unification_Types : UNIFICATION_TYPES =
struct

type unifier = Context.generic -> term * term -> Envir.env -> (Envir.env * thm)

end