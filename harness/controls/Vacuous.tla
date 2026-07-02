---- MODULE Vacuous ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == UNCHANGED x  \* 1 reachable state; cfg lists no invariant.
====
