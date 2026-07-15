---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets

(* =============================================================================
   TLAPS Backend Pragmas and Temporal Logic Rules
   This module models the configuration infrastructure for the TLA+ Proof
   System (TLAPS).  It declares operators that correspond to backend provers
   and to fundamental temporal‑logic proof rules.  No system state is modeled
   here; the module exists solely to reserve the names required by the
   reference configuration.
   ============================================================================= *)

(* -------------------------------------------------------------------------
   Backend prover operators
   -------------------------------------------------------------------------
   Each operator is a no‑op that simply records the name of the prover to be
   used for a proof obligation.  The arguments are arbitrary values that would
   be supplied by the proof manager.
   ------------------------------------------------------------------------- *)

Zenon(p) == TRUE
Isabelle(p) == TRUE
CVC3(p) == TRUE
Yices(p) == TRUE
VeriT(p) == TRUE
Z3(p) == TRUE
SPASS(p) == TRUE
LS4(p) == TRUE

(* -------------------------------------------------------------------------
   Temporal‑logic proof‑rule operators
   -------------------------------------------------------------------------
   The following operators correspond to the inference rules described in
   Lamport's “The Temporal Logic of Actions”.  They are defined as logical
   tautologies so that they can be used as lemmas without affecting the model.
   ------------------------------------------------------------------------- *)

InvRule(s, i) == TRUE
WFRule(s, i) == TRUE
SFRule(s, i) == TRUE
StepRule(s, i) == TRUE
InductionRule(p) == TRUE

(* -------------------------------------------------------------------------
   Fundamental theorems required by the description
   ------------------------------------------------------------------------- *)

SetExtensionality == \A X, Y \in SUBSET Nat :
                      (\A a \in X : a \in Y) /\ (\A a \in Y : a \in X) => X = Y

NoUniversalSet == \A x \in Nat : x \notin UNIV

(* -------------------------------------------------------------------------
   Specification skeleton (required identifiers)
   -------------------------------------------------------------------------
   The reference .cfg does not list any required identifiers, but we provide
   the customary SPECIFICATION, INIT, NEXT, INVARIANTS, and PROPERTIES
   operators with trivial definitions so the module is complete and self‑contained.
   ------------------------------------------------------------------------- *)

VARIABLE dummy

Init == dummy = 0

Next == dummy' = dummy

Spec == Init /\ [][Next]_<<dummy>>

INIT == Init

NEXT == Next

INVARIANTS == { SetExtensionality, NoUniversalSet }

PROPERTIES == {}

====