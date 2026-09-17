----------------------------- MODULE mathd_numbertheory_483 -----------------------------
EXTENDS TLAPS, Integers


THEOREM mathd_numbertheory_483 ==
  \A a \in [Nat -> Nat] :
    (a[1] = 1 /\ a[2] = 1 /\ \A n \in Nat : a[n + 2] = a[n + 1] + a[n])
    => a[100] % 4 = 3BY SMT, SetExtensionality
================================================================================
