----- MODULE exercise_3_4 -----
EXTENDS Integers, TLAPS

THEOREM exercise_3_4 ==
  ~(\E x, y \in Int : 3*(x*x) + 2 = y*y)BY SMT
=============================================
