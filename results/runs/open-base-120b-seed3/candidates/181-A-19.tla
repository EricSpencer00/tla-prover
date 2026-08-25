---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

(* Finite version of the natural numbers for model checking *)
NatOverride == 0 .. MaxNat

VARIABLE n

(* Initial state predicate *)
INIT == n \in NatOverride

(* Next-state relation *)
NEXT == /\ n' \in NatOverride
        /\ n' = n + 1

(* Overall specification *)
SPECIFICATION == INIT /\ [][NEXT]_<<n>>

(* State invariant *)
TypeInvariant == n \in NatOverride

INVARIANTS == TypeInvariant

(* Property asserting that the double of any number in NatOverride is even *)
DoubleEven == \A m \in NatOverride : (2 * m) % 2 = 0

PROPERTIES == DoubleEven
====