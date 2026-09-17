---- MODULE numbertheory_aoddbdiv4asqpbsqmod8eq1 ----
EXTENDS Integers, TLAPS

Divides(i, j) == \E k \in Int : j = i * k

THEOREM numbertheory_aoddbdiv4asqpbsqmod8eq1 ==
  \A a \in Int, b \in Nat :
    (a % 2 = 1) /\ Divides(4, b) => (a*a + b*b) % 8 = 1
BY SMT
====
