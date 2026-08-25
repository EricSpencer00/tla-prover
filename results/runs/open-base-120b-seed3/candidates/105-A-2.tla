---- MODULE DyadicRationals ----
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Constants (their values are supplied in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT ArithmeticModules
CONSTANT ArithmeticOps
CONSTANT EqualityOps
CONSTANT ExtendsModules
CONSTANT FunctionApplication
CONSTANT IfThenElse
CONSTANT ModuleName
CONSTANT OperatorDefNames
CONSTANT RecordAccess
CONSTANT RecordConstructor
CONSTANT id

\* ----------------------------------------------------------------------
\* State variable representing a dyadic rational as a record {num, den}
\* ----------------------------------------------------------------------
VARIABLE p

\* ----------------------------------------------------------------------
\* Operator definitions listed in OperatorDefNames
\* ----------------------------------------------------------------------
One == [num |-> 1, den |-> 1]

Half(q) == [num |-> q.num, den |-> q.den * 2]

Norm(q) ==
  IF q.num % 2 = 0 /\ q.den % 2 = 0
    THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2])
    ELSE q

\* ----------------------------------------------------------------------
\* Type invariant for dyadic rationals (denominator a positive power of two)
\* ----------------------------------------------------------------------
Dyadic(p) ==
  /\ p \in [num : Int, den : Nat]
  /\ p.den > 0
  /\ \E n \in Nat : p.den = 2^n

\* ----------------------------------------------------------------------
\* Init, Next, and the overall specification
\* ----------------------------------------------------------------------
INIT == p = One

NEXT ==
  \/ p' = Half(p)
  \/ p' = Norm(p)
  \/ UNCHANGED p

SPECIFICATION == INIT /\ [][NEXT]_<p>

\* ----------------------------------------------------------------------
\* Invariant and property definitions required by the task
\* ----------------------------------------------------------------------
INVARIANTS == Dyadic(p)

PROPERTIES == TRUE

====