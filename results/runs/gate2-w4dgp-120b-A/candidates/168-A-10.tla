---- MODULE ReadersWriters ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS NumActors

Actors == 1 .. NumActors
Modes == {"Read", "Write"}
Requests == [actor : Actors, mode : Modes]

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ Cardinality(writers) <= 1
    /\ queue \in Seq(Requests)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = <<>>

\* A process requests read access; if already waiting to read it is not re-queued.
RequestRead(p) ==
    /\ \A i \in DOMAIN queue : !(queue[i].actor = p /\ queue[i].mode = "Read")
    /\ \A i \in DOMAIN queue : !(queue[i].actor = p /\ queue[i].mode = "Write")
    /\ queue' = Append(queue, [actor |-> p, mode |-> "Read"])
    /\ UNCHANGED <<readers, writers>>

\* A process requests write access; if already waiting to write it is not re-queued.
RequestWrite(p) ==
    /\ \A i \in DOMAIN queue : !(queue[i].actor = p /\ queue[i].mode = "Write")
    /\ \A i \in DOMAIN queue : !(queue[i].actor = p /\ queue[i].mode = "Read")
    /\ queue' = Append(queue, [actor |-> p, mode |-> "Write"])
    /\ UNCHANGED <<readers, writers>>

\* Take the request at the head of the queue and grant access based on capacity.
ProcessQueue ==
    /\ queue # <<>>
    /\ writers = {}
    /\ readers = {}
    /\ LET r == Head(queue) IN
        /\ IF r.mode = "Read"
              THEN readers' = readers \cup {r.actor}
              ELSE readers' = readers
        /\ IF r.mode = "Write"
              THEN writers' = writers \cup {r.actor}
              ELSE writers' = writers
        /\ queue' = Tail(queue)

\* An active reader stops.
StopRead(p) ==
    /\ p \in readers
    /\ readers' = readers \ {p}
    /\ UNCHANGED <<writers, queue>>

\* An active writer stops.
StopWrite(p) ==
    /\ p \in writers
    /\ writers' = writers \ {p}
    /\ UNCHANGED <<readers, queue>>

Next ==
    \/ \E p \in Actors : RequestRead(p) \/ RequestWrite(p) \/ StopRead(p) \/ StopWrite(p)
    \/ ProcessQueue

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in Actors : RequestRead(p))
    /\ WF_vars(\E p \in Actors : RequestWrite(p))
    /\ WF_vars(ProcessQueue)
    /\ \A p \in Actors : WF_vars(StopRead(p))
    /\ \A p \in Actors : WF_vars(StopWrite(p))

\* Readers and writers never go at the same time.
Safety ==
    /\ (readers # {} => writers = {})
    /\ (writers # {} => readers = {})
    /\ Cardinality(writers) <= 1

Liveness ==
    /\ \A p \in Actors : <>(p \in readers)
    /\ \A p \in Actors : <>(p \in writers)
    /\ \A p \in Actors : <>(p \notin readers)
    /\ \A p \in Actors : <>(p \notin writers)

====