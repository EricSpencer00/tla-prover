---- MODULE MC_sums_even ----
CONSTANTS MaxNat, Nat

VARIABLE v

(* Initial state: set v to 0, which is an element of the bounded natural numbers *)
Init == v = 0

(* Next action: stutter, keep v unchanged *)
Next == v' = v

(* Specification *)
Spec == Init /\ [][Next]_v

(* Safety invariant: the double of any natural number is even *)
EvenDouble == \A n \in Nat : ((2*n) \bmod 2) = 0

(* Operators required by the reference configuration *)
SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == EvenDouble
PROPERTIES == {}

====