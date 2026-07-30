---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Actors == 1 .. NumActors

NONE == "none"
Reqs == [type : {"read", "write"}, who : Actors]

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ queue \in Seq(Reqs)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = <<>>

RequestRead(a) ==
    /\ ~ \E i \in 1 .. Len(queue) : queue[i].who = a
    /\ queue' = Append(queue, [type |-> "read", who |-> a])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(a) ==
    /\ ~ \E i \in 1 .. Len(queue) : queue[i].who = a
    /\ queue' = Append(queue, [type |-> "write", who |-> a])
    /\ UNCHANGED <<readers, writers>>

BeginServe ==
    /\ queue # <<>>
    /\ writers = {}
    /\ LET r == Head(queue) IN
        /\ IF r.type = "read" THEN readers' = readers \cup {r.who} ELSE readers' = readers
        /\ IF r.type = "write" /\ readers = {} THEN writers' = writers \cup {r.who} ELSE writers' = writers
        /\ queue' = Tail(queue)

StopActivity(a) ==
    /\ \/ a \in readers
       \/ a \in writers
    /\ readers' = readers \ {a}
    /\ writers' = writers \ {a}
    /\ UNCHANGED queue

Next ==
    \/ \E a \in Actors : RequestRead(a) \/ RequestWrite(a) \/ StopActivity(a)
    \/ BeginServe

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E a \in Actors : RequestRead(a))
    /\ WF_vars(\E a \in Actors : RequestWrite(a))
    /\ WF_vars(BeginServe)
    /\ WF_vars(\E a \in Actors : StopActivity(a))

\* Safety: readers and writers are never active at the same time, and at most
\* one writer is active -- both are implied by the single active-writer set.
Safety ==
    /\ readers # {}
       => writers = {}
    /\ writers # {}
       => readers = {}
    /\ Cardinality(writers) <= 1

Liveness ==
    /\ \A a \in Actors : (a \in readers) ~> (a \notin readers)
    /\ \A a \in Actors : (a \in writers) ~> (a \notin writers)

====