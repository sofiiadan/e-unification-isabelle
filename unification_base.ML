(*  Title:      E_Unification/unification_base.ML
    Author:     Kevin Kappelmann

Basic definitions for unifiers.
*)

signature UNIFICATION_BASE =
sig
  val reflexive : cterm -> thm
  val combination : thm -> thm -> thm
  val symmetric : thm -> thm
  val abstract_rule : string -> cterm -> thm -> thm
  val reflexive_term : Proof.context -> term -> thm

  (*raised on unsupported input*)
  exception PATTERN

  (*raised on unification failure for non-sequence outputs*)
  exception UNIF
  type unifier = Proof.context -> term * term -> Envir.env -> (Envir.env * thm) Seq.seq

  (*raised on matching failure*)
  exception MATCH
  (*TODO: change to same type as unifier*)
  (* type matcher = Proof.context -> term * term -> Envir.env -> (Envir.env * thm) *)
  type matcher = theory -> term * term -> Type.tyenv * Envir.tenv -> Type.tyenv * Envir.tenv
end

structure Unification_Base : UNIFICATION_BASE =
struct

val reflexive = Thm.reflexive
val combination = Thm.combination
val symmetric = Thm.symmetric
val abstract_rule = Thm.abstract_rule

val reflexive_term = reflexive oo Thm.cterm_of

exception PATTERN = Pattern.Pattern

exception UNIF = Pattern.Unif
type unifier = Proof.context -> term * term -> Envir.env -> (Envir.env * thm) Seq.seq

exception MATCH = Pattern.MATCH
(* type matcher = Proof.context -> term * term -> Envir.env -> (Envir.env * thm) *)
type matcher = theory -> term * term -> Type.tyenv * Envir.tenv -> Type.tyenv * Envir.tenv

end