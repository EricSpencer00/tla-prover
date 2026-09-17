----- MODULE imo_1993_p5 -----
EXTENDS TLAPS, Naturals

THEOREM imo_1993_p5 ==
    \E f \in [Nat -> Nat] :
        f[1] = 2 /\
        (\A n \in Nat : f[f[n]] = f[n] + n) /\
        (\A n \in Nat : f[n] < f[n + 1])BY SMT
=============================================================================
