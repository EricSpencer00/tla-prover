---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

(* Finite version of the natural numbers for model checking *)
NatOverride == 0 .. MaxNat

VARIABLE n

(* Initial condition *)
INIT == n \in NatOverride

(* Nondeterministic step: choose any natural number in the finite range *)
NEXT == n' \in NatOverride

(* Helper definition for evenness *)
IsEven(m) == \E k \in NatOverride : m = 2 * k

(* Property: double of any natural number is even *)
EvenDouble == IsEven(2 * n)

(* Overall specification *)
SPECIFICATION == INIT /\ [][NEXT]_<<n>>

(* State invariants to be checked by TLC *)
INVARIANTS == { EvenDouble }

(* Temporal properties (none needed beyond the invariant) *)
PROPERTIES == {}

====