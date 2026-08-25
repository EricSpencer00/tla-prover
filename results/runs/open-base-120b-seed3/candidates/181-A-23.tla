---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

VARIABLE n

(* Initial state: n ranges over the finite Nat *)
Init == n \in NatOverride

(* Next-state relation: nondeterministically choose any value in NatOverride *)
Next == n' \in NatOverride

(* Standard specification operators *)
SPECIFICATION == Init /\ [][Next]_n
INIT == Init
NEXT == Next
INVARIANTS == n \in NatOverride

(* Property: the double of any natural number in NatOverride is even *)
PROPERTIES == \A m \in NatOverride : Even(2 * m)

====