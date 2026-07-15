---- MODULE MC_sums_even ----
CONSTANT MaxNat, Nat

(* Invariant: the double of any natural number is even *)
DoubleIsEven == \A n \in Nat : ((n + n) % 2 = 0)

Init == TRUE
Next == TRUE

Spec == Init /\ [][Next]_<<>>

INVARIANTS == {DoubleIsEven}
PROPERTIES == {}
====