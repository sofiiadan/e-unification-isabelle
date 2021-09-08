(*  Title:      Unification_Hints/unification_types.ML
    Author:     Kevin Kappelmann

Shared type definitions for unifiers.
*)

signature UNIFICATION_TYPES =
sig
  exception Unif
  type unifier = Context.generic -> term * term -> Envir.env -> Envir.env * thm

  exception MATCH
  (* type matcher = Context.generic -> term * term -> Envir.env -> (Envir.env * thm) *)
  type matcher = theory -> term * term -> Type.tyenv * Envir.tenv -> Type.tyenv * Envir.tenv
end

structure Unification_Types : UNIFICATION_TYPES =
struct

exception Unif
type unifier = Context.generic -> term * term -> Envir.env -> Envir.env * thm

exception MATCH
(* type matcher = Context.generic -> term * term -> Envir.env -> (Envir.env * thm) *)
type matcher = theory -> term * term -> Type.tyenv * Envir.tenv -> Type.tyenv * Envir.tenv

end