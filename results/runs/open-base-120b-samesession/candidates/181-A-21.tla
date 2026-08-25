---- MODULE MC_sums_even ----
EXTENDS Naturals, TLC

CONSTANT MaxNat

(* A finite version of the natural numbers, used for model checking *)
NatOverride == 0 .. MaxNat

VARIABLE n

(* Initial state: n is any natural number in the finite range *)
Init == n \in NatOverride

(* Next-state relation: n may take any value in the finite range *)
Next == n' \in NatOverride

(* The overall specification *)
SPECIFICATION == Init /\ [][Next]_<<n>>

(* Required identifiers *)
INIT == Init
NEXT == Next

(* The theorem: the double of any natural number is even *)
EvenDouble == \A n \in NatOverride : \E k \in NatOverride : 2 * n = 2 * k

INVARIANTS == { EvenDouble }

PROPERTIES == {}

====