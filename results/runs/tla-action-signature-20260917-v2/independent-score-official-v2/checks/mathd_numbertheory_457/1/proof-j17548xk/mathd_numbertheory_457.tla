---- MODULE mathd_numbertheory_457 ----
EXTENDS TLAPS, Integers, NaturalsInduction

factorial[n \in Nat] == IF n = 0 THEN 1 ELSE n * factorial[n-1]

THEOREM FactorialDefConclusion == NatInductiveDefConclusion(factorial, 1, LAMBDA v,n : n*v)
<1>1. NatInductiveDefHypothesis(factorial, 1, LAMBDA v,n : n*v)
  BY DEF NatInductiveDefHypothesis, factorial
<1>2. QED
  BY <1>1, NatInductiveDef

THEOREM FactorialDef == \A n \in Nat : factorial[n] = IF n = 0 THEN 1 ELSE n * factorial[n-1]
BY FactorialDefConclusion DEF NatInductiveDefConclusion

Divides(a, b) == \E k \in Nat : b = a * k

THEOREM mathd_numbertheory_457 ==
  \A n \in Nat :
    (n > 0 /\ Divides(80325, factorial[n])) => (n >= 17)BY SMT DEF Divides
====
