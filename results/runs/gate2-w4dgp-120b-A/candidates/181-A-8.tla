---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

NatOverride == 0..MaxNat

ASSUME MaxNat \in Nat
ASSUME MaxNat > 0

VARIABLES x, y

vars == <<x, y>>

Init ==
  /\ x = 0
  /\ y = 0

Step ==
  /\ x < MaxNat
  /\ x' = x + 1
  /\ y' = (x + 1) + (x + 1)
  /\ UNCHANGED y

SpecChoice == Init /\ [][Step]_vars

StateSpace == SpecChoice

====