---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat, Nat

(* Override the infinite set of natural numbers with a finite range *)
NatAssumption == Nat = 0..MaxNat

(* The base theorem: the double of any natural number is even *)
DoubleIsEven == \A n \in Nat : \E k \in Nat : 2 * k = 2 * n

(* The theorem is taken as an assumption for model checking *)
THEOREM_Assume == DoubleIsEven

(* Declare the specification operators required by the .cfg *)
VARIABLE x

(* Initial state: pick any natural number in the bounded set *)
Init == x \in Nat

(* Next action: nondeterministically assign any (possibly the same) natural number *)
Next == x' \in Nat

(* Init and Next combined into the Spec */
Spec == Init /\ [][Next]_<<x>>

(* The property we want to check: the double of the current value is even *)
EvenDouble == \E k \in Nat : 2 * k = 2 * x

(* The property is invariant under the Spec *)
Invariant == EvenDouble

(* The property is also a temporal property (for completeness) *)
Property == <>EvenDouble

====