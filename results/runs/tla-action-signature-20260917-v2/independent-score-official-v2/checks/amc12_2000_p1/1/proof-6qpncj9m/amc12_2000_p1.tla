----- MODULE amc12_2000_p1 -----
EXTENDS Naturals, TLAPS


THEOREM amc12_2000_p1 ==
    \A I, M, O \in Nat : (I # M /\ M # O /\ O # I /\ I * M * O = 2001) => (I + M + O <= 671)BY SMT
====
