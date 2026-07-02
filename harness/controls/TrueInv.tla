---- MODULE TrueInv ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3  \* bounded (3 reachable states), so TLC actually terminates
Inv == TRUE  \* syntactically present, real state changes, but checks nothing: MUST be flagged
====
