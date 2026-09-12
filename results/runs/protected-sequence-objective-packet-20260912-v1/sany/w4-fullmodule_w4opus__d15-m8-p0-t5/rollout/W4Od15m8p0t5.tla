---- MODULE W4Od15m8p0t5 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Traders, Books, Admin, None

VARIABLES coarseLock, fineLocks, lockHolder, adminHolding

vars == << coarseLock, fineLocks, lockHolder, adminHolding >>

TypeOK ==
    /\ coarseLock \in {None, Admin, \cup {t \in Traders : t \in lockHolder}}
    /\ fineLocks \in [Books -> {None, Admin, \cup {t \in Traders : t \in lockHolder}}]
    /\ lockHolder \subseteq Traders \cup {Admin}
    /\ adminHolding \in {None, Admin}

Init ==
    /\ coarseLock = None
    /\ fineLocks = [b \in Books |-> None]
    /\ lockHolder = {}
    /\ adminHolding = None

Next ==
    /\ coarseLock' = IF coarseLock = None \/ coarseLock = Admin
                      THEN coarseLock
                      ELSE IF \E t \in Traders : t \in lockHolder
                            THEN coarseLock
                            ELSE None
    /\ \A b \in Books : fineLocks'[b] = IF fineLocks[b] = None
                                     THEN None
                                     ELSE IF fineLocks[b] = coarseLock
                                          THEN fineLocks[b]
                                          ELSE IF fineLocks[b] = Admin
                                               THEN fineLocks[b]
                                               ELSE None
    /\ lockHolder' = IF coarseLock = None
                      THEN lockHolder
                      ELSE IF coarseLock = Admin
                            THEN lockHolder
                            ELSE IF coarseLock \in Traders
                                  THEN {coarseLock} \cup lockHolder
                                  ELSE {}
    /\ adminHolding' = IF coarseLock = Admin
                      THEN Admin
                      ELSE adminHolding

LockHierarchy == coarseLock \in lockHolder \cup {Admin} /\ \A b \in Books : fineLocks[b] \in lockHolder \cup {Admin}

Spec == Init /\ [][Next]_vars

====