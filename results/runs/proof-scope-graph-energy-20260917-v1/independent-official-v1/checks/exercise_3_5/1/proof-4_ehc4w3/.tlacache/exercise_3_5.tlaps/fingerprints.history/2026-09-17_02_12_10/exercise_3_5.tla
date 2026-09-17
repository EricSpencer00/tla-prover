----- MODULE exercise_3_5 -----
EXTENDS TLAPS, Integers

THEOREM exercise_3_5 ==
  ~ (\E x, y \in Int : 7 * x*x*x + 2 = y*y*y)BY NoSetContainsEverything
====
