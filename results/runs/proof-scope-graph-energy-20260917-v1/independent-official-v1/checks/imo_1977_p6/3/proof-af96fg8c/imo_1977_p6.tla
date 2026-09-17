----- MODULE imo_1977_p6 -----
EXTENDS Naturals, TLAPS

THEOREM imo_1977_p6 ==
    \A f \in [Nat -> Nat] :
        (\A n \in Nat : (f[n] > 0)) /\
        (\A n \in Nat : (n > 0) => (f[f[n]] < f[n + 1]))
        => (\A n \in Nat : (n > 0) => (f[n] = n))BY SMT
====
