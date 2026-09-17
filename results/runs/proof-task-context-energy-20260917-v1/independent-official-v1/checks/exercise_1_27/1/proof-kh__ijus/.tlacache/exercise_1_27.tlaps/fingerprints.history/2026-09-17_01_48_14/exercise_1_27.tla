---- MODULE exercise_1_27 ----
EXTENDS Naturals, TLAPS

Odd(n) == n % 2 = 1
Divides(a, b) == \E k \in Nat : b = a * k

THEOREM exercise_1_27 ==
  \A n \in Nat :
    Odd(n) => Divides(8, (n * n - 1))
BY SMT DEF Odd, Divides
====
