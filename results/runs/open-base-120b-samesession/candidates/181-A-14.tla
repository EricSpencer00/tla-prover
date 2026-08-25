---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

(* Finite version of the natural numbers for model checking *)
NatOverride == 0 .. MaxNat

(* No state variables are needed for this configuration module *)
INIT == TRUE

NEXT == UNCHANGED <<>>

SPECIFICATION == INIT /\ [][NEXT]_<<>>

IsEven(x) == x % 2 = 0

Theorem == \A n \in NatOverride : IsEven(2 * n)

INVARIANTS == Theorem

PROPERTIES == Theorem
====