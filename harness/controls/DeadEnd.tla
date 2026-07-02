---- MODULE DeadEnd ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1  \* no successor at x = 2: TLC MUST report deadlock
Inv == x <= 2
====
