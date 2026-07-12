---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

VARIABLES
    provers, timeouts, tactics

(* ----------------------------------------------------------------------
   Helper definitions for the backend provers
   ---------------------------------------------------------------------- *)

ProverSet == {Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4}

(* Each prover may have an associated timeout (in seconds) and a tactic *)
Timeouts == [p \in ProverSet |-> 30]   \* default timeout
Tactics  == [p \in ProverSet |-> "default"]

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)

provers == ProverSet
timeouts == Timeouts
tactics  == Tactics

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)

Init ==
    /\ provers = ProverSet
    /\ timeouts = Timeouts
    /\ tactics  = Tactics

(* ----------------------------------------------------------------------
   Actions (none, as this module is purely declarative)
   ---------------------------------------------------------------------- *)

Next == UNCHANGED <<provers, timeouts, tactics>>

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<provers, timeouts, tactics>>

(* ----------------------------------------------------------------------
   Safety properties (theorems)
   ---------------------------------------------------------------------- *)

SetExtensionality ==
    \A s, t \in SUBSET UNIV :
        (\A x \in UNIV : (x \in s) = (x \in t)) => s = t

NoSetContainsAll ==
    \A s \in SUBSET UNIV : s # UNIV

(* ----------------------------------------------------------------------
   Liveness properties (none)
   ---------------------------------------------------------------------- *)

(* ----------------------------------------------------------------------
   Theorems (for TLC, we declare them as invariants)
   ---------------------------------------------------------------------- *)

THEOREM SetExtensionality_Inv == []SetExtensionality
THEOREM NoSetContainsAll_Inv == []NoSetContainsAll

====