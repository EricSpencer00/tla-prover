---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* State variables: readers, writers, and the waiting queue of (read/write, actor)
VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

Actors == 1..NumActors
Requests == [kind: {"read", "write"}, actor: Actors]

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ queue \in Seq(Requests)

\* Readers and writers are never active at the same time
Safety ==
    /\ (writers # {} => readers = {})
    /\ (readers # {} => writers = {})
    /\ Cardinality(writers) <= 1

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = <<>>

RequestToRead(a) ==
    /\ \A i \in 1..Len(queue): queue[i].actor # a
    /\ queue' = Append(queue, [kind |-> "read", actor |-> a])
    /\ UNCHANGED <<readers, writers>>

RequestToWrite(a) ==
    /\ \A i \in 1..Len(queue): queue[i].actor # a
    /\ queue' = Append(queue, [kind |-> "write", actor |-> a])
    /\ UNCHANGED <<readers, writers>>

BeginAccess ==
    /\ queue # {}
    /\ writers = {}
    /\ LET r == Head(queue) IN
        /\ IF r.kind = "read"
           THEN readers' = readers \cup {r.actor}
           ELSE IF readers = {} THEN writers' = writers \cup {r.actor} ELSE writers' = writers
        /\ queue' = Tail(queue)
    /\ UNCHANGED writers

StopActivity(a) ==
    /\ readers' = readers \ {a}
    /\ writers' = writers \ {a}
    /\ UNCHANGED queue

Next ==
    \/ \E a \in Actors: RequestToRead(a)
    \/ \E a \in Actors: RequestToWrite(a)
    \/ \E a \in Actors: StopActivity(a)
    \/ BeginAccess

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A a \in Actors: WF_vars(RequestToRead(a))
    /\ \A a \in Actors: WF_vars(RequestToWrite(a))
    /\ WF_vars(BeginAccess)
    /\ \A a \in Actors: WF_vars(StopActivity(a))

\* Every actor eventually reads and eventually writes
Liveness ==
    \A a \in Actors: (a \in readers) ~> (a \in writers)

\* Every active reader/writer eventually stops
EventualQuiescence ==
    \A a \in Actors: (a \in readers \/ a \in writers) ~> (a \notin readers /\ a \notin writers)
====