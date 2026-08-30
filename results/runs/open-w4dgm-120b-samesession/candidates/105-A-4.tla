---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS ArithmeticModules, ArithmeticOps, EqualityOps, ExtendsModules, FunctionApplication,
    IfThenElse, OperatorDefNames, RecordAccess, RecordConstructor, Specification, id

None == "none"

VARIABLES p, pending, active

vars == <<p, pending, active>>

TypeOK ==
    /\ p \in [num : Nat, den : Nat]
    /\ pending \in [active -> BOOLEAN]

Init ==
    /\ p = [num |-> 1, den |-> 1]
    /\ pending = {}
    /\ active = None

Request ==
    /\ active = None
    /\ active' = "active"
    /\ pending' = {}
    /\ UNCHANGED <<p>>

ClaimTerminate(rr) ==
    /\ active # None
    /\ rr \notin pending
    /\ pending' = pending \cup {rr}
    /\ UNCHANGED <<p, active>>

Terminate(rr) ==
    /\ rr \in pending
    /\ pending' = pending \ {rr}
    /\ active' = None
    /\ UNCHANGED <<p>>

Half ==
    /\ p' = [num |-> p.num, den |-> p.den * 2]
    /\ UNCHANGED <<pending, active>>

Norm ==
    /\ active # None
    /\ IF p.num % 2 = 0 /\ p.den % 2 = 0
         THEN p' = [num |-> p.num \div 2, den |-> p.den \div 2]
         ELSE p' = p
    /\ UNCHANGED <<pending, active>>

Next ==
    \/ Request
    \/ \E rr \in {"rr1", "rr2"} : ClaimTerminate(rr)
    \/ \E rr \in {"rr1", "rr2"} : Terminate(rr)
    \/ Half
    \/ Norm

Spec == Init /\ [][Next]_vars

DenominatorPowerOfTwo ==
    \E k \in Nat : p.den = 2^k

====