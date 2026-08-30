---- MODULE DyadicRationals ----
INTEGER == Integers

ExtendsModules == ["Integers"]
Operators == {"*" : (INTEGER, INTEGER) :> INTEGER,
              "\\" : (INTEGER, INTEGER) :> INTEGER,
              "%" : (INTEGER, INTEGER) :> INTEGER,
              "=" : (INTEGER, INTEGER) :> BOOLEAN}

CONSTANTS ArithmeticModules, ArithmeticOps, EqualityOps
Operators == [op \in ArithmeticOps \cup EqualityOps |-> Operators[op]]

RECURSIVE GCD(_)
GCD(a) == IF a = 0 THEN 1 ELSE a
GCD(a, b) == IF b = 0 THEN GCD(a) ELSE GCD(b, a % b)

VARIABLES p

TypeOK ==
  /\ p \in [num : INTEGER, den : INTEGER]
  /\ p.num >= 0 /\ p.den > 0

Init ==
  /\ p = [num |-> 1, den |-> 1]

One == [num |-> 1, den |-> 1]

Half == [num |-> p.num, den |-> p.den * 2]

Norm(x) == IF x.den % 2 = 0 /\ x.num % 2 = 0
           THEN Norm([num |-> x.num \div 2, den |-> x.den \div 2])
           ELSE x

Next ==
  /\ p' \in [num : INTEGER, den : INTEGER]
  /\ p' = Norm([num |-> p.num * 3, den |-> p.den])

Spec == Init /\ [][Next]_p
====