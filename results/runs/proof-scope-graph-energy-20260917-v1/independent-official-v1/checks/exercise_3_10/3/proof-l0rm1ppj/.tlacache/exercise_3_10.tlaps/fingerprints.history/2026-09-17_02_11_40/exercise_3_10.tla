---- MODULE exercise_3_10 ----
EXTENDS TLAPS, Integers, NaturalsInduction

factorial[n \in Nat] == IF n = 0 THEN 1 ELSE n * factorial[n-1]

THEOREM FactorialDefConclusion == NatInductiveDefConclusion(factorial, 1, LAMBDA v,n : n*v)
<1>1. NatInductiveDefHypothesis(factorial, 1, LAMBDA v,n : n*v)
  BY DEF NatInductiveDefHypothesis, factorial
<1>2. QED
  BY <1>1, NatInductiveDef

THEOREM FactorialDef == \A n \in Nat : factorial[n] = IF n = 0 THEN 1 ELSE n * factorial[n-1]
BY FactorialDefConclusion DEF NatInductiveDefConclusion


IsPrime(n) ==    (n > 1)
              /\ \A m \in 2..(n-1) : ~ \E p \in 2..(n-1) : n = m * p

THEOREM exercise_3_10 ==
  \A n \in Nat :
    (~IsPrime(n) /\ n # 4) =>
    (factorial[n - 1] % n = 0)BY SMT, FactorialDefConclusion, FactorialDef, DownwardNatInduction
====
