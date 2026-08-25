---- MODULE MC_sums_even ----
EXTENDS Naturals, TLC

CONSTANT MaxNat

(* Finite version of the natural numbers for model checking *)
NatOverride == 0 .. MaxNat

VARIABLE n

(* Initial state: n is any natural number within the finite bound *)
INIT == n \in NatOverride

(* Next-state relation: nondeterministically choose any bounded natural number *)
NEXT == 
    /\ n' \in NatOverride

(* Overall specification used by TLC *)
SPECIFICATION == INIT /\ [][NEXT]_<<n>>

(* Helper predicate: a number is even if it is twice some bounded natural *)
IsEven(m) == \E k \in NatOverride : m = 2 * k

(* Invariant that the double of the current n is even *)
Invariant == IsEven(2 * n)

(* Property stating that the double of every bounded natural number is even *)
PROPERTIES == \A m \in NatOverride : IsEven(2 * m)

====