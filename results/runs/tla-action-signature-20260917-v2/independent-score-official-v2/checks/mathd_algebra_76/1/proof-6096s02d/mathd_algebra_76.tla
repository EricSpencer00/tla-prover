----- MODULE mathd_algebra_76 -----
EXTENDS Integers, TLAPS

Even(n) == n % 2 = 0
Odd(n) == n % 2 = 1

THEOREM mathd_algebra_76 ==
    \A f \in [Int -> Int] :
        (\A n \in Int : (Odd(n) => (f[n] = n*n))) /\
        (\A n \in Int: (Even(n) => (f[n] = n*n - 4*n - 1))) =>
        f[4] = -1BY SMT DEF Even, Odd
================================
