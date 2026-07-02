---- MODULE Counter ----
EXTENDS Integers
VARIABLE
  \* @type: Int;
  x
Init == x = 0
Next == x' = x + 1
Inv == x >= 0
====
