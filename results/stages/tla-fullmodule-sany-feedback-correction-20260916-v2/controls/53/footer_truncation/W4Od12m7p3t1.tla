------------------------------ MODULE W4Od12m7p3t1 ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Slots, Units, MaxInbox, MaxVersion

AllRequests == [slot : Slots, unit : Units]

VARIABLES inbox, grants, done, version
vars == <<inbox, grants, done, version>>

Init ==
    /\ inbox = {}
    /\ grants = {}
    /\ done = {}
    /\ version = 0

Arrive(r) ==
    /\ r \in AllRequests
    /\ r \notin inbox
    /\ r \notin grants
    /\ r \notin done
    /\ Cardinality(inbox) < MaxInbox
    /\ inbox' = inbox \cup {r}
    /\ UNCHANGED <<grants, done, version>>

CommitCAS(r) ==
    /\ r \in inbox
    /\ version < MaxVersion
    /\ \A g \in grants : g.slot # r.slot
    /\ grants' = grants \cup {r}
    /\ inbox' = inbox \ {r}
    /\ version' = version + 1
    /\ UNCHANGED done

Reject(r) ==
    /\ r \in inbox
    /\ \E g \in grants : g.slot = r.slot
    /\ inbox' = inbox \ {r}
    /\ UNCHANGED <<grants, done, version>>

Release(r) ==
    /\ r \in grants
    /\ grants' = grants \ {r}
    /\ done' = done \cup {r}
    /\ UNCHANGED <<inbox, version>>

Recycle ==
    /\ inbox = {}
    /\ grants = {}
    /\ done # {}
    /\ done' = {}
    /\ version' = 0
    /\ UNCHANGED <<inbox, grants>>

Next ==
    \/ Recycle
    \/ \E r \in AllRequests :
         Arrive(r) \/ CommitCAS(r) \/ Reject(r) \/ Release(r)

Spec == Init /\ [][Next]_vars

NoDoubleGrant ==
    \A g1, g2 \in grants : (g1.slot = g2.slot) => (g1 = g2)

GrantsArchiveDisjoint ==
    grants \cap done = {}

===