---- MODULE amc12a_2021_p8 ----
EXTENDS Naturals, TLAPS

D[n \in Nat] == IF n = 0 THEN 0
                ELSE IF n = 1 THEN 0
                ELSE IF n = 2 THEN 1
                ELSE D[n-1] + D[n-3]

Even(x) == x % 2 = 0
Odd(x)  == x % 2 = 1

THEOREM amc12a_2021_p8 ==
    Even(D[2021]) /\ Odd(D[2022]) /\ Even(D[2023])BY SMT DEF Even, Odd
====
