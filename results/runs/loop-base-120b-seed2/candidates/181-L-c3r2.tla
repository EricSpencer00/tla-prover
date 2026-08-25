---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

(* Evenness definition using a fast arithmetic test *)
Even(m) == m % 2 = 0

VARIABLE n

(* Initial state: n is a natural number within the bounded range *)
Init == n \in NatOverride

(* Nondeterministic step: n may take any value in the bounded range *)
Next == n' \in NatOverride

(* Full specification for TLC *)
SPECIFICATION == Init /\ [][Next]_<<n>>

(* Safety invariant that should hold in every reachable state *)
INVARIANTS == Even(2 * n)

(* Global property asserting the theorem for all numbers in the finite range *)
PROPERTIES == \A m \in NatOverride : Even(2 * m)

====