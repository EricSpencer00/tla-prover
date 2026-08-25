---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

(* Finite version of the natural numbers for model checking *)
NatOverride == 0 .. MaxNat

VARIABLE n

(* Initial state predicate required by TLC *)
Init == n \in NatOverride

(* Next-state action required by TLC *)
Next == n' \in NatOverride

(* Helper definition for evenness *)
IsEven(m) == \E k \in NatOverride : m = 2 * k

(* Property: double of any natural number is even *)
EvenDouble == IsEven(2 * n)

(* Overall specification *)
Spec == Init /\ [][Next]_<<n>>

(* State invariants to be checked by TLC *)
INVARIANTS == { EvenDouble }

(* Temporal properties (none needed beyond the invariant) *)
PROPERTIES == {}

====