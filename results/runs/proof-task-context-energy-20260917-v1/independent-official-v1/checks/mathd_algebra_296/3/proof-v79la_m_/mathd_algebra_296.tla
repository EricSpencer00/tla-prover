---- MODULE mathd_algebra_296 ----
EXTENDS Integers, TLAPS


ABS(x) == IF x < 0 THEN -x ELSE x

THEOREM mathd_algebra_296 ==
    ABS((3491 - 60) * (3491 + 60) - 3491 * 3491) = 3600BY SMT
====
