---- MODULE UnreachableNext ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x = 0 /\ x = 1 /\ x' = x  \* self-contradictory guard: never enabled, even from Init
Inv == x >= 0
====
