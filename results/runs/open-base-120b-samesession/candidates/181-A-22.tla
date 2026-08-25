---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

(* Finite version of the natural numbers, used to bound the model *)
NatOverride == 0 .. MaxNat

VARIABLE n

(* Initial state: n is any natural within the bounded range *)
INIT == n \in NatOverride

(* Next-state relation: n may take any value within the bounded range *)
NEXT == n' \in NatOverride

(* Full specification for TLC *)
SPECIFICATION == INIT /\ [][NEXT]_<<n>>

(* Definition of evenness using the bounded naturals *)
Even(x) == \E m \in NatOverride : x = 2 * m

(* Constant‑level assumption: the double of any natural number is even *)
ASSUME TheoremAssumption == \A n \in NatOverride : Even(2 * n)

(* Invariants to be checked by TLC *)
INVARIANTS == { TheoremAssumption }

(* Additional temporal properties (none required) *)
PROPERTIES == {}

====