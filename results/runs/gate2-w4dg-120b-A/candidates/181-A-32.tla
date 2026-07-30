---- MODULE MC_sums_even ----
EXTENDS Integers

CONSTANTS MaxNat, Nat

RECURSIVE Double(_)
Double(n) ==
  IF n = 0 THEN 0
  ELSE 2 + Double(n - 1)

ASSUME Nat = 0..MaxNat

TheoremAlwaysHolds == \A n \in Nat : Double(n) % 2 = 0

Spec == TheoremAlwaysHolds

SpecOK == Spec

Init == TheoremAlwaysHolds

Next == Unchanged Nat

SpecInv == TheoremAlwaysHolds

StateConstraint == TheoremAlwaysHolds

Spec == Spec /\ Init /\ [][Next]_Nat /\ SpecInv /\ StateConstraint
====