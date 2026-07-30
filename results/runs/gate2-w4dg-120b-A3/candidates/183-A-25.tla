---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANT Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

VARIABLES steps
vars == <<steps>>

TypeOK == steps \in Nat

Init == steps = 0

NExt == steps' = (steps + 1) % 2
Done == steps = 0 /\ steps' = 0

ZenonProve(ax) == TRUE
IsabelleProve(ax) == TRUE
CVC3Prove(ax) == TRUE
YicesProve(ax) == TRUE
VeriTProve(ax) == TRUE
Z3Prove(ax) == TRUE
SPASSProve(ax) == TRUE
LS4Prove(ax) == TRUE

Spec == Init /\ [][NExt]_vars /\ WF_vars(Done)

Extensionality == \A x \in {s \in SUBSET {1, 2, 3} : Cardinality(s) = 2} :
                    \A y \in {t \in SUBSET {1, 2, 3} : Cardinality(t) = 2} :
                      (x = y) <=> (\A e \in {1, 2, 3} : e \in x <=> e \in y)

NoSetContainsAll == \A x \in {s \in SUBSET {1, 2, 3} : Cardinality(s) = 2} : x # {1, 2, 3}
====