------------------------------- MODULE numbertheory_4x3m7y3neq2003 -------------------------------
EXTENDS Integers, TLAPS

THEOREM numbertheory_4x3m7y3neq2003 ==
  \A x, y \in Int :
    4 * x * x * x - 7 * y * y * y # 2003
BY SMT
====================================================================================================
