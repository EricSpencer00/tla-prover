---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* A process is in the queue with a kind (read/write) and its own identifier.
Request == [kind: {"read", "write"}, who: 1..NumActors]

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

TypeOK ==
    /\ readers \subseteq (1..NumActors)
    /\ writers \subseteq (1..NumActors)
    /\ queue \in Seq(Request)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = << >>

\* A process cannot queue the same kind twice; it must finish first.
RequestRead(i) ==
    /\ \A k \in 1..Len(queue): queue[k].who # i
    /\ queue' = Append(queue, [kind |-> "read", who |-> i])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(i) ==
    /\ \A k \in 1..Len(queue): queue[k].who # i
    /\ queue' = Append(queue, [kind |-> "write", who |-> i])
    /\ UNCHANGED <<readers, writers>>

\* Begin happens only when the front request's action is currently free.
BeginAccess ==
    /\ queue # << >>
    /\ writers = {}
    /\ LET m == Head(queue) IN
        /\ IF m.kind = "read" THEN readers' = readers \cup {m.who}
           ELSE /\ writers' = writers \cup {m.who}
                /\ readers' = readers
        /\ queue' = Tail(queue)

StopActivity(i) ==
    /\ \/ readers' = readers \ {i}
       \/ writers' = writers \ {i}
    /\ UNCHANGED queue

Next ==
    \/ \E i \in 1..NumActors: RequestRead(i)
    \/ \E i \in 1..NumActors: RequestWrite(i)
    \/ BeginAccess
    \/ \E i \in 1..NumActors: StopActivity(i)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E i \in 1..NumActors: RequestRead(i))
        /\ WF_vars(\E i \in 1..NumActors: RequestWrite(i))
        /\ WF_vars(BeginAccess)
        /\ WF_vars(\E i \in 1..NumActors: StopActivity(i))

Safety ==
    /\ readers # {} => writers = {}
    /\ Cardinality(writers) <= 1

Liveness ==
    /\ \A i \in 1..NumActors: (i \in readers) ~> (i \notin readers)
    /\ \A i \in 1..NumActors: (i \in writers) ~> (i \notin writers)

====