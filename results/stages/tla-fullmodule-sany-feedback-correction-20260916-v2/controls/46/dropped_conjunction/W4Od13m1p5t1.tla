---- MODULE W4Od13m1p5t1 ----
EXTENDS Naturals
CONSTANT Machines
VARIABLES grant, dispensed
vars == <<grant, dispensed>>

Init ==
  /\ grant = (CHOOSE m \in Machines : TRUE)
    dispensed = [m \in Machines |-> 0]

PassToRing(m) ==
  /\ grant = m
  /\ grant' = "ring"
  /\ UNCHANGED dispensed

Deliver(m) ==
  /\ grant = "ring"
  /\ grant' = m
  /\ UNCHANGED dispensed

Dispense(m) ==
  /\ grant = m
  /\ dispensed[m] = 0
  /\ dispensed' = [dispensed EXCEPT ![m] = dispensed[m] + 1]
  /\ grant' = "ring"

Next == \E m \in Machines : PassToRing(m) \/ Deliver(m) \/ Dispense(m)
Spec == Init /\ [][Next]_vars

DispensedAtMostOnce == \A m \in Machines : dispensed[m] <= 1
====