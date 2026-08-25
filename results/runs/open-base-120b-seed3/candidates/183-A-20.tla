---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(* ----------------------------------------------------------------------
   Backend prover identifiers (place‑holders – actual configuration is
   handled by the proof manager, not by the model itself).
   ---------------------------------------------------------------------- *)
CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

(* ----------------------------------------------------------------------
   Trivial state to make a well‑formed behavioural specification.
   ---------------------------------------------------------------------- *)
VARIABLE dummy

Init == TRUE

Next == UNCHANGED dummy

SPECIFICATION == Init /\ [][Next]_<<dummy>>

INVARIANTS == {}

PROPERTIES == {}

(* ----------------------------------------------------------------------
   Fundamental theorems required by the description
   ---------------------------------------------------------------------- *)

(* Set extensionality: two sets are equal iff they have the same elements. *)
EXTENSIONALITY ==
  \A S, T \in SUBSET UNIV :
    (\A x \in UNIV : (x \in S) \iff (x \in T)) => S = T

(* No set contains every possible value. *)
NoUniversalSet ==
  \A S \in SUBSET UNIV : \E x \in UNIV : x \notin S

THEOREM SetExtensionality == EXTENSIONALITY
THEOREM NoSetContainsAllValues == NoUniversalSet

====