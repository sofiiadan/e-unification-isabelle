(*  Title:      Unification_Hints/unification_types.ML
    Author:     Kevin Kappelmann

Shared type definitions for unifiers.
*)

signature UNIFICATION_TYPES =
sig
  (*raised on unsupported input*)
  exception PATTERN

  exception UNIF
  type unifier = Context.generic -> term * term -> Envir.env -> Envir.env * thm

  exception MATCH
  (*TODO: change to same type as unifier*)
  (* type matcher = Context.generic -> term * term -> Envir.env -> (Envir.env * thm) *)
  type matcher = theory -> term * term -> Type.tyenv * Envir.tenv -> Type.tyenv * Envir.tenv
end

structure Unification_Types : UNIFICATION_TYPES =
struct

exception PATTERN = Pattern.Pattern

exception UNIF = Pattern.Unif
type unifier = Context.generic -> term * term -> Envir.env -> Envir.env * thm

exception MATCH = Pattern.MATCH
(* type matcher = Context.generic -> term * term -> Envir.env -> (Envir.env * thm) *)
type matcher = theory -> term * term -> Type.tyenv * Envir.tenv -> Type.tyenv * Envir.tenv

end