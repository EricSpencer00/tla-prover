---- MODULE W4Od6m7p1t2 ----
EXTENDS Integers

Instances == {"A", "B"}
Recs      == {"nCall", "sCall"}
Vals      == {"v1", "v2"}
MAXV      == 3
NONE      == "none"

VARIABLES version, value, lastSnap, snap, have
vars == <<version, value, lastSnap, snap, have>>

Init ==
    /\ version  = [r \in Recs |-> 0]
    /\ value    = [r \in Recs |-> NONE]
    /\ lastSnap = [r \in Recs |-> 0]
    /\ snap     = [i \in Instances |-> [r \in Recs |-> 0]]
    /\ have     = [i \in Instances |-> [r \in Recs |-> FALSE]]

Read(i, r) ==
    /\ snap' = [snap EXCEPT ![i][r] = version[r]]
    /\ have' = [have EXCEPT ![i][r] = TRUE]
    /\ UNCHANGED <<version, value, lastSnap>>

Commit(i, r, val) ==
    /\ have[i][r]
    /\ snap[i][r] = version[r]
    /\ version[r] < MAXV
    /\ value'    = [value    EXCEPT ![r] = val]
    /\ version'  = [version  EXCEPT ![r] = version[r] + 1]
    /\ lastSnap' = [lastSnap EXCEPT ![r] = snap[i][r]]
    /\ have'     = [have EXCEPT ![i][r] = FALSE]
    /\ UNCHANGED snap

Reject(i, r) ==
    /\ have[i][r]
    /\ snap[i][r] # version[r]
    /\ have' = [have EXCEPT ![i][r] = FALSE]
    /\ UNCHANGED <<version, value, lastSnap, snap>>

Refresh(r) ==
    /\ version[r] < MAXV
    /\ value'    = [value    EXCEPT ![r] = NONE]
    /\ lastSnap' = [lastSnap EXCEPT ![r] = version[r]]
    /\ version'  = [version  EXCEPT ![r] = version[r] + 1]
    /\ UNCHANGED <<snap, have>>

Next ==
    \/ \E i \in Instances, r \in Recs : Read(i, r)
    \/ \E i \in Instances, r \in Recs, val \in Vals : Commit(i, r, val)
    \/ \E i \in Instances, r \in Recs : Reject(i, r)
    \/ \E r \in Recs : Refresh(r)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ version  \in [Recs -> 0..MAXV]
    /\ value    \in [Recs -> Vals \cup {NONE}]
    /\ lastSnap \in [Recs -> 0..MAXV]
    /\ snap     \in [Instances -> [Recs -> 0..MAXV]]
    /\ have     \in [Instances -> [Recs -> BOOLEAN]]

NoLostUpdate ==
    \A r \in Recs : (version[r] > 0) => (lastSnap[r] = version[r] - 1)
====