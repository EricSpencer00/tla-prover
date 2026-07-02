---- MODULE ProofSmoke ----
EXTENDS Naturals, TLAPS

THEOREM OnePlusOne == 1 + 1 = 2
OBVIOUS

THEOREM Tautology == \A p \in BOOLEAN : p \/ ~p
OBVIOUS

====
