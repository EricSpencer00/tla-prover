----------------------------- MODULE 1_Consensus ------------------------------ 
\* benchmark: tla-consensus

EXTENDS Naturals, FiniteSets, FiniteSetTheorems

CONSTANT Value 
  (*************************************************************************)
  (* The set of all values that can be chosen.                             *)
  (*************************************************************************)
  
VARIABLE chosen
  (*************************************************************************)
  (* The set of all values that have been chosen.                          *)
  (*************************************************************************)
  
(***************************************************************************)
(* The type-correctness invariant.                                         *)
(***************************************************************************)
TypeOK == /\ chosen \in SUBSET Value

(***************************************************************************)
(* The initial predicate and next-state relation.                          *)
(***************************************************************************)
Init == chosen = {}

Next == /\ chosen = {}
        /\ \E v \in Value : chosen' = {v}

Inv == /\ TypeOK
       /\ Cardinality(chosen) \leq 1

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Inv

ASSUME Fin == IsFiniteSet(Value)

THEOREM Inductiveness ==IndAuto /\ Next => IndAuto'OBVIOUS
=============================================================================
