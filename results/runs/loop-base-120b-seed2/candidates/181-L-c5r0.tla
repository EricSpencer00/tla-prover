---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

(* Finite version of the natural numbers set for model checking *)
NatOverride == 0 .. MaxNat

VARIABLE n

(* Initial state: n is any natural number within the finite range *)
Init == n \in NatOverride

(* Next-state relation: increment n while staying within the bound, or stutter *)
Next == 
    \/ /\ n < MaxNat
       /\ n' = n + 1
    \/ /\ n' = n

(* Overall specification *)
Spec == Init /\ [][Next]_<<n>>

(* Definition of evenness using the finite NatOverride set *)
Even(m) == \E k \in NatOverride : m = 2 * k

(* State invariant: double of n is even *)
DoubleIsEven == Even(2 * n)

SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == << DoubleIsEven >>
PROPERTIES == [] DoubleIsEven
====