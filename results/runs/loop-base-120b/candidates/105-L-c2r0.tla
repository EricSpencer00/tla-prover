---- MODULE DyadicRationals ----
EXTENDS Integers

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
    Specification,
    id

(*--- Constant definitions ---*)
ArithmeticModules == {"Integers"}
ArithmeticOps == {"*", "\div", "%"}
EqualityOps == {"="}
ExtendsModules == {"Integers"}
FunctionApplication == {"Norm([num |-> p.num \\div 2, den |-> p.den \\div 2])"}
IfThenElse == {"IF p.num % 2 = 0 /\\ p.den % 2 = 0 THEN Norm([num |-> p.num \\div 2, den |-> p.den \\div 2]) ELSE p (in Norm)"}
ModuleName == "DyadicRationals"
OperatorDefNames == {"One", "Half", "Norm"}
RecordAccess == {"p.num", "p.den"}
RecordConstructor == {"[num |-> 1, den |-> 1]", "[num |-> p.num, den |-> p.den * 2]", "[num |-> p.num \\div 2, den |-> p.den \\div 2]"}
Specification == "Dyadic rationals with recursive normalization"
id == 105

(*--- Dyadic rational definitions ---*)
Dyadic == [num : Int, den : Nat]

One == [num |-> 1, den |-> 1]

Half(p) == [num |-> p.num, den |-> p.den * 2]

RECURSIVE Norm(_)
Norm(p) ==
    IF (p.num % 2 = 0) /\ (p.den % 2 = 0) THEN
        Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

(*--- Required specification operators ---*)
SPECIFICATION == TRUE

INIT == TRUE

NEXT == UNCHANGED <<>>

INVARIANTS == {}

PROPERTIES == {}

====