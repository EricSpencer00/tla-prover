---- MODULE exercise_1_1_4 ----
EXTENDS TLAPS, Integers

THEOREM exercise_1_1_4 ==
  \A a, b, c, n \in Nat :
    \E k \in Nat :
       (a * b) * c - a * (b * c) = k * nBY SMT, NoSetContainsEverything, SetExtensionality
====
