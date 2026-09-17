---- MODULE aimeII_2001_p3 ----
EXTENDS Naturals, Integers, TLAPS


THEOREM aimeII_2001_p3 ==
    \A x \in [Nat -> Int] : (x[1] = 211) /\ (x[2] = 375) /\ (x[3] = 420) /\ (x[4] = 523) /\ (\A n \in Nat : n >= 5 => x[n] = x[n - 1] - x[n - 2] + x[n - 3] - x[n - 4]) => (x[531] + x[753] + x[975] = 898)BY SMT
====
