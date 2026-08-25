---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

(* NatOverride replaces Nat with a finite version for model checking *)
NatOverride == 0 .. MaxNat

VARIABLE n

Init == n \in NatOverride

Next == n' = n

SPECIFICATION == Init /\ [] [Next]_<<n>>

INVARIANTS == TRUE

PROPERTIES == TRUE
====