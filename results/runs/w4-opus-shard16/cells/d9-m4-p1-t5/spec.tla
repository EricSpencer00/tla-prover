-------------------------- MODULE W4Od9m4p1t5 --------------------------
EXTENDS Naturals, Sequences

CONSTANTS Cap, MaxVer

VARIABLES
    version,    \* live version of the shared setpoint record
    lastBase,   \* base version the latest committed change was built on
    queue       \* bounded FIFO of pending updates, each a base-version stamp

vars == << version, lastBase, queue >>

Update == [base : 0..MaxVer]

TypeOK ==
    /\ version \in 0..MaxVer
    /\ lastBase \in 0..MaxVer
    /\ queue \in Seq(Update)
    /\ Len(queue) <= Cap

Init ==
    /\ version = 0
    /\ lastBase = 0
    /\ queue = << >>

\* A producer enqueues, stamping the version it currently observes.
Enqueue ==
    /\ Len(queue) < Cap
    /\ queue' = Append(queue, [base |-> version])
    /\ UNCHANGED << version, lastBase >>

\* The consumer applies the head when its base is still current.
ApplyMatch ==
    /\ queue # << >>
    /\ Head(queue).base = version
    /\ version < MaxVer
    /\ version' = version + 1
    /\ lastBase' = Head(queue).base
    /\ queue' = Tail(queue)

\* The consumer rejects a stale head rather than letting it clobber state.
RejectStale ==
    /\ queue # << >>
    /\ (Head(queue).base # version \/ version = MaxVer)
    /\ queue' = Tail(queue)
    /\ UNCHANGED << version, lastBase >>

\* Admin override: flush all pending and directly apply one change.
AdminOverride ==
    /\ version < MaxVer
    /\ version' = version + 1
    /\ lastBase' = version
    /\ queue' = << >>

Next ==
    \/ Enqueue
    \/ ApplyMatch
    \/ RejectStale
    \/ AdminOverride

Spec == Init /\ [][Next]_vars

\* No lost updates: the latest committed change built on its predecessor.
NoLostUpdate == (version = 0) \/ (lastBase = version - 1)

=============================================================================
