---- MODULE MC_sums_even ----
EXTENDS Naturals, Sequences, TLC

CONSTANT MaxNat
CONSTANT Nat

(* There are no mutable state variables in this specification *)
VARIABLES

Init == TRUE

Next == TRUE

SPECIFICATION == Init /\ []Next

INVARIANTS == {}

PROPERTIES == {}

====