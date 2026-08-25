---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

VARIABLE n

(* Initial condition: n ranges over the finite natural numbers *)
INIT == n \in NatOverride

(* Next-state relation: increment n until MaxNat, then stay *)
NEXT == 
  /\ n \in NatOverride
  /\ n' = IF n < MaxNat THEN n + 1 ELSE n

(* Full specification for TLC *)
SPECIFICATION == INIT /\ [][NEXT]_<<n>>

(* Invariant stating that double of any n is even *)
INVARIANTS == (2 * n) % 2 = 0

(* Property to be checked: the invariant holds always *)
PROPERTIES == [] (2 * n) % 2 = 0

====