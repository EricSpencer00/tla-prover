---- MODULE imo_1982_p1 ----
EXTENDS TLAPS, Integers


THEOREM imo_1982_p1 ==
    \A f \in [Nat -> Nat] :
        (\A m, n \in Nat \ {0} : (f[m + n] - f[m] - f[n] = 0) \/ (f[m + n] - f[m] - f[n] = 1)) /\
        (f[2] = 0) /\ (f[3] > 0) /\ (f[9999] = 3333)
        => (f[1982] = 660)BY SetExtensionality
====
