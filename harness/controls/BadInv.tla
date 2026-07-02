---- MODULE BadInv ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + 1
Inv == x < 3  \* violated at x = 3: TLC MUST report an invariant violation
====
