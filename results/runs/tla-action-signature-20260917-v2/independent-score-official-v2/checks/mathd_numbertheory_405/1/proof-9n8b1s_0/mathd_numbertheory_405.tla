----- MODULE mathd_numbertheory_405 -----
EXTENDS TLAPS, Integers

THEOREM mathd_numbertheory_405 ==
    \A a, b, c \in Nat : \A t \in [Nat -> Nat] :
        (t[0] = 0) /\ (t[1] = 1) /\
        (\A n \in Nat: n > 1 => t[n] = t[n-2] + t[n-1]) /\
        (a % 16 = 5) /\ (b % 16 = 10) /\ (c % 16 = 15) =>
        (t[a] + t[b] + t[c]) % 7 = 5BY SMT
=============================================================================
