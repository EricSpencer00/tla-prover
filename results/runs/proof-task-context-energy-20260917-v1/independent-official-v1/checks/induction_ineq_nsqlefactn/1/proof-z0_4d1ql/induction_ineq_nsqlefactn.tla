---- MODULE induction_ineq_nsqlefactn ----
EXTENDS TLAPS, Integers, NaturalsInduction

factorial[n \in Nat] == IF n = 0 THEN 1 ELSE n * factorial[n-1]

THEOREM FactorialDefConclusion == NatInductiveDefConclusion(factorial, 1, LAMBDA v,n : n*v)
<1>1. NatInductiveDefHypothesis(factorial, 1, LAMBDA v,n : n*v)
  BY DEF NatInductiveDefHypothesis, factorial
<1>2. QED
  BY <1>1, NatInductiveDef

THEOREM FactorialDef == \A n \in Nat : factorial[n] = IF n = 0 THEN 1 ELSE n * factorial[n-1]
BY FactorialDefConclusion DEF NatInductiveDefConclusion


THEOREM induction_ineq_nsqlefactn ==
    \A n \in Nat :
        n >= 4 =>
        n * n <= factorial[n]BY FactorialDefConclusion, FactorialDef, DownwardNatInduction
=============================================================
