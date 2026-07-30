---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Actors == 1..NumActors
Mode == {"read", "write"}

VARIABLES readers, writers, queue
vars == <<readers, writers, queue>>

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = << >>

Enqueue(f, p) ==
    /\ Len(queue) < NumActors
    /\ queue' = Append(queue, [mode |-> f, pid |-> p])
    /\ UNCHANGED <<readers, writers>>

RequestRead(p) ==
    /\ \A i \in 1..Len(queue) : queue[i].pid # p
    /\ Enqueue("read", p)

RequestWrite(p) ==
    /\ \A i \in 1..Len(queue) : queue[i].pid # p
    /\ Enqueue("write", p)

BeginAccess ==
    /\ Len(queue) > 0
    /\ writers = {}
    /\ LET head == Head(queue) IN
        IF head.mode = "read" THEN
            /\ readers' = readers \cup {head.pid}
            /\ queue' = Tail(queue)
            /\ UNCHANGED writers
        ELSE
            /\ readers = {}
            /\ writers' = writers \cup {head.pid}
            /\ queue' = Tail(queue)
            /\ UNCHANGED readers

StopActivity(p) ==
    /\ \/ p \in readers /\ readers' = readers \ {p}
       \/ p \in writers /\ writers' = writers \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in Actors : RequestRead(p)
    \/ \E p \in Actors : RequestWrite(p)
    \/ BeginAccess
    \/ \E p \in Actors : StopActivity(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in Actors : RequestRead(p))
    /\ WF_vars(\E p \in Actors : RequestWrite(p))
    /\ WF_vars(BeginAccess)
    /\ \A p \in Actors : WF_vars(StopActivity(p))

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ Cardinality(writers) <= 1
    /\ Len(queue) <= NumActors

Safety ==
    /\ (writers # {} => readers = {})
    /\ \A p, q \in writers : p = q

Liveness ==
    /\ \A p \in Actors : (p \in readers) ~> (p \notin readers)
    /\ \A p \in Actors : (p \in writers) ~> (p \notin writers)

====