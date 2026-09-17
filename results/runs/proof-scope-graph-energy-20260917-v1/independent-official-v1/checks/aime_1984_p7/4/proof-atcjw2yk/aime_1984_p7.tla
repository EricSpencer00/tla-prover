---- MODULE aime_1984_p7 ----
EXTENDS TLAPS, Integers

f[n \in Int] == IF n >= 1000 THEN n - 3 ELSE f[f[n + 5]]

THEOREM aime_1984_p7 == f[84] = 997BY SMT, NoSetContainsEverything
============================================================
