---- MODULE DyadicRationals ----
EXTENDS Integers
CONSTANTS ArithmeticModules, ArithmeticOps, EqualityOps, ExtendsModules, FunctionApplication, IfThenElse, OperatorDefNames, RecordAccess, RecordConstructor, Specification, id

One == [num |-> 1, den |-> 1]
Half == [num |-> 1, den |-> 2]

RECURSIVE Norm(_)
Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2]) ELSE p

VARIABLES val

vars == <<val>>

TypeOK == /\ val \in {One} \union {Half} \union [num : Nat, den : Nat]

Init == /\ val = One

Halve == /\ val # Half
         /\ val' = [num |-> val.num, den |-> val.den * 2]
         /\ UNCHANGED <<>>

Reduce == /\ val' = Norm(val)
          /\ UNCHANGED <<>>

Next == Halve \/ Reduce

Spec == Init /\ [][Next]_vars

DenNonZero == val.den # 0

RationalRepresentationsConverge ==
  \A p \in {One, Half} : (p = Half) <=> (p.den = 2)
====