(*  Title:      E_Unification/unification_base.ML
    Author:     Kevin Kappelmann

Basic definitions for unifiers.
*)

signature UNIFICATION_BASE =
sig
  include HAS_LOGGER

  val reflexive : cterm -> thm
  val combination : thm -> thm -> thm
  val symmetric : thm -> thm
  val transitive : thm -> thm -> thm
  val abstract_rule : string -> cterm -> thm -> thm
  val reflexive_term : Proof.context -> term -> thm

  (*raised on unsupported input*)
  exception PATTERN

  (*raised on unification failure for non-sequence outputs*)
  exception UNIF
  type type_unifier = Proof.context -> typ * typ -> Envir.env -> Envir.env
  type type_matcher = type_unifier
  type unifier = Proof.context -> term * term -> Envir.env -> (Envir.env * thm) Seq.seq
  type matcher = unifier
end

structure Unification_Base : UNIFICATION_BASE =
struct

val logger = Logger.setup_new_logger Logger.root_logger "Unif"

val reflexive = Thm.reflexive
val combination = Thm.combination
val symmetric = Thm.symmetric
val transitive = Thm.transitive
val abstract_rule = Thm.abstract_rule

val reflexive_term = reflexive oo Thm.cterm_of

exception PATTERN = Pattern.Pattern

exception UNIF = Pattern.Unif
type type_unifier = Proof.context -> typ * typ -> Envir.env -> Envir.env
type type_matcher = type_unifier
type unifier = Proof.context -> term * term -> Envir.env -> (Envir.env * thm) Seq.seq
type matcher = unifier

end
