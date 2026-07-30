---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

VARIABLES readers, writers, queue
vars == <<readers, writers, queue>>

Waiting == {"read", "write"}

Requests == { [kind |-> k, pid |-> p] : k \in Waiting, p \in 1..NumActors }

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = << >>

RequestRead(p) ==
    /\ [kind |-> "read", pid |-> p] \notin { queue[i] : i \in DOMAIN queue }
    /\ queue' = Append(queue, [kind |-> "read", pid |-> p])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
    /\ [kind |-> "write", pid |-> p] \notin { queue[i] : i \in DOMAIN queue }
    /\ queue' = Append(queue, [kind |-> "write", pid |-> p])
    /\ UNCHANGED <<readers, writers>>

BeginAccess ==
    /\ queue # << >>
    /\ writers = {}
    /\ LET front == Head(queue) IN
        /\ front.kind = "read"
           \/ (front.kind = "write" /\ readers = {})
        /\ readers' = IF front.kind = "read" THEN readers \cup {front.pid} ELSE readers
        /\ writers' = IF front.kind = "write" THEN writers \cup {front.pid} ELSE writers
        /\ queue' = Tail(queue)

StopActivity(p) ==
    /\ \/ p \in readers
       \/ p \in writers
    /\ readers' = readers \ {p}
    /\ writers' = writers \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in 1..NumActors : RequestRead(p)
    \/ \E p \in 1..NumActors : RequestWrite(p)
    \/ BeginAccess
    \/ \E p \in 1..NumActors : StopActivity(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in 1..NumActors : RequestRead(p))
    /\ WF_vars(\E p \in 1..NumActors : RequestWrite(p))
    /\ WF_vars(BeginAccess)
    /\ WF_vars(\E p \in 1..NumActors : StopActivity(p))

TypeOK ==
    /\ readers \subseteq (1..NumActors)
    /\ writers \subseteq (1..NumActors)
    /\ \A i \in DOMAIN queue: queue[i] \in Requests

Safety ==
    /\ (writers # {} => readers = {})
    /\ (readers # {} => writers = {})
    /\ writers # {} => Cardinality(writers) = 1

Liveness ==
    /\ \A p \in 1..NumActors : (p \in readers) ~> (p \notin readers)
    /\ \A p \in 1..NumActors : (p \in writers) ~> (p \notin writers)

\* Queue capacity is bounded to keep the model finite; the bound itself is finite.
BoundedQueue ==
    /\ Len(queue) <= NumActors

====