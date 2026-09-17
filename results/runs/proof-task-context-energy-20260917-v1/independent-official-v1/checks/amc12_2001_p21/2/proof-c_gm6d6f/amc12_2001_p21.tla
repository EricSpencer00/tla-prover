---- MODULE amc12_2001_p21 ----
EXTENDS Integers, TLAPS

THEOREM amc12_2001_p21 ==
  \A a, b, c, d \in Int :
    (a > 0 /\ b > 0 /\ c > 0 /\ d > 0 /\
     a * b * c * d = 8 * 7 * 6 * 5 * 4 * 3 * 2 * 1 /\
     a * b + a + b = 524 /\
     b * c + b + c = 146 /\
     c * d + c + d = 104) =>
     a - d = 10BY SetExtensionality
====
