---- MODULE MC_sums_even ----
EXTENDS Naturals, FiniteSets

CONSTANTS MaxNat, Nat

(* ----------------------------------------------------------------------
   Override the infinite natural number set with a finite range
   ---------------------------------------------------------------------- *)
Nat == 0 .. MaxNat

(* ----------------------------------------------------------------------
   Theorem: the double of any natural number is even
   ---------------------------------------------------------------------- *)
THEOREM DoubleIsEven == 
  \A n \in Nat : (2 * n) % 2 = 0

(* ----------------------------------------------------------------------
   Safety property: the theorem holds for all reachable states
   ---------------------------------------------------------------------- *)
Safety == DoubleIsEven

(* ----------------------------------------------------------------------
   Liveness property: the system never deadlocks (trivially true)
   ---------------------------------------------------------------------- *)
Liveness == []<>TRUE

(* ----------------------------------------------------------------------
   Specification: no state changes, only the safety property is checked
   ---------------------------------------------------------------------- *)
SPECIFICATION Spec == Safety

(* ----------------------------------------------------------------------
   Initial state: the theorem holds initially
   ---------------------------------------------------------------------- *)
INIT Init == Safety

(* ----------------------------------------------------------------------
   Next-state relation: no state changes
   ---------------------------------------------------------------------- *)
NEXT Next == UNCHANGED <<>>

(* ----------------------------------------------------------------------
   Invariant: the theorem holds in every reachable state
   ---------------------------------------------------------------------- *)
INVARIANT Safety

(* ----------------------------------------------------------------------
   Properties: the safety property is the only property to check
   ---------------------------------------------------------------------- *)
PROPERTIES Safety

====