-------------------------- MODULE W4Od13m1p1t2 --------------------------
EXTENDS Naturals, TLC

CONSTANTS MaxVer

\* Fixed ring of three machines: n1,n2 (instance A) and n3 (instance B).
Nodes == {"n1", "n2", "n3"}
Succ == ("n1" :> "n2" @@ "n2" :> "n3" @@ "n3" :> "n1")

VARIABLES
    token,      \* the machine currently holding the write token
    version,    \* live version of the shared inventory record
    lastBase,   \* base version the latest committed update was built on
    snap        \* snap[n] : version machine n last read

vars == << token, version, lastBase, snap >>

TypeOK ==
    /\ token \in Nodes
    /\ version \in 0..MaxVer
    /\ lastBase \in 0..MaxVer
    /\ snap \in [Nodes -> 0..MaxVer]

Init ==
    /\ token = "n1"
    /\ version = 0
    /\ lastBase = 0
    /\ snap = [n \in Nodes |-> 0]

\* The token is passed to the ring successor.
PassToken ==
    /\ token' = Succ[token]
    /\ UNCHANGED << version, lastBase, snap >>

\* Any machine may read the record and snapshot the version.
Read(n) ==
    /\ snap' = [snap EXCEPT ![n] = version]
    /\ UNCHANGED << token, version, lastBase >>

\* Commit requires holding the token and a still-current snapshot.
Commit(n) ==
    /\ token = n
    /\ snap[n] = version
    /\ version < MaxVer
    /\ version' = version + 1
    /\ lastBase' = snap[n]
    /\ UNCHANGED << token, snap >>

\* At the cap, the token holder recycles the record to a fresh baseline.
Recycle(n) ==
    /\ token = n
    /\ version = MaxVer
    /\ version' = 0
    /\ lastBase' = 0
    /\ snap' = [m \in Nodes |-> 0]
    /\ UNCHANGED token

Next ==
    \/ PassToken
    \/ \E n \in Nodes : Read(n)
    \/ \E n \in Nodes : Commit(n)
    \/ \E n \in Nodes : Recycle(n)

Spec == Init /\ [][Next]_vars

\* No lost updates: each committed update built on its immediate predecessor.
NoLostUpdate == (version = 0) \/ (lastBase = version - 1)

=============================================================================
