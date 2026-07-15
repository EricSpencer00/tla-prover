---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat, Nat

VARIABLES v

(* ----------------------------------------------------------------------
   State definition
   ---------------------------------------------------------------------- *)

Init ==
    /\ v \in Nat
    /\ v = 0

Next ==
    v' = (v + 1) % (MaxNat + 1)

Spec ==
    Init /\ [][Next]_<<v>>

(* ----------------------------------------------------------------------
   Assertions
   ---------------------------------------------------------------------- *)

EvenDouble ==
    \A n \in Nat : (2 * n) % 2 = 0

(* ----------------------------------------------------------------------
   Declaration of the specification components
   ---------------------------------------------------------------------- *)

SPECIFICATION Spec
INIT Init
NEXT Next
INVARIANTS EvenDouble
PROPERTIES TRUE

====