------------------------------- MODULE mathd_algebra_392 -------------------------------
EXTENDS TLAPS, Integers

Even(x) == x % 2 = 0

THEOREM mathd_algebra_392 ==
    \A n \in Nat :
        Even(n) /\
        (n - 2) * (n - 2) + n * n + (n + 2) * (n + 2) = 12296 =>
        (n - 2) * n * (n + 2) = 32736 * 8
BY SMT DEF Even
=============================================================================
