---- MODULE DyadicRationals ----
EXTENDS Integers

\* -------------------------------------------------
\* Metadata constants (as required)
\* -------------------------------------------------
CONSTANTS
    ArithmeticModules,
    ArithmeticOps,
    EqualityOps,
    ExtendsModules,
    FunctionApplication,
    IfThenElse,
    ModuleName,
    OperatorDefNames,
    RecordAccess,
    RecordConstructor,
    id

\* Assign concrete values to the metadata constants
ASSUME /\ ArithmeticModules = {"Integers"}
       /\ ArithmeticOps = {"*","\\div","%"}
       /\ EqualityOps = {"="}
       /\ ExtendsModules = {"Integers"}
       /\ FunctionApplication = {"Norm([num |-> p.num \\div 2, den |-> p.den \\div 2])"}
       /\ IfThenElse = {"IF p.num % 2 = 0 /\\ p.den % 2 = 0 THEN Norm([num |-> p.num \\div 2, den |-> p.den \\div 2]) ELSE p (in Norm)"}
       /\ ModuleName = "DyadicRationals"
       /\ OperatorDefNames = {"One","Half","Norm"}
       /\ RecordAccess = {"p.num","p.den"}
       /\ RecordConstructor = {"[num |-> 1, den |-> 1]",
                               "[num |-> p.num, den |-> p.den * 2]",
                               "[num |-> p.num \\div 2, den |-> p.den \\div 2]"}
       /\ id = 105

\* -------------------------------------------------
\* Core dyadic rational definitions
\* -------------------------------------------------
Dyadic == [num : Int, den : Nat]

One == [num |-> 1, den |-> 1]

Half(p) == [num |-> p.num, den |-> p.den * 2]

RECURSIVE Norm(_)

Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

\* -------------------------------------------------
\* State variables and behavior
\* -------------------------------------------------
VARIABLE r

INIT == r = One

NEXT ==
    \/ r' = Norm(Half(r))
    \/ r' = r

SPECIFICATION == INIT /\ [][NEXT]_<<r>>

\* -------------------------------------------------
\* Invariant and property definitions
\* -------------------------------------------------
Invariant == r.den > 0

INVARIANTS == Invariant

PROPERTIES == TRUE
====