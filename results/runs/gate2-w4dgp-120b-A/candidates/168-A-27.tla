---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Actors == 1..NumActors

InitQueue == << >>

Requests == [actor: Actors, kind: {"read", "write"}]

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ queue \in (Requests)^*

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = InitQueue

RequestRead(a) ==
    /\ [actor |-> a, kind |-> "read"] \notin queue
    /\ queue' = Append(queue, [actor |-> a, kind |-> "read"])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(a) ==
    /\ [actor |-> a, kind |-> "write"] \notin queue
    /\ queue' = Append(queue, [actor |-> a, kind |-> "write"])
    /\ UNCHANGED <<readers, writers>>

ProcessQueue ==
    /\ Len(queue) > 0
    /\ queue[1].kind = "read" \/ readers = {}
    /\ writers = {}
    /\ LET head == Head(queue)
       IN readers' = IF head.kind = "read" THEN readers \cup {head.actor} ELSE readers
          /\ writers' = IF head.kind = "write" THEN writers \cup {head.actor} ELSE writers
    /\ queue' = Tail(queue)

StopActivity(a) ==
    /\ (a \in readers \/ a \in writers)
    /\ readers' = readers \ {a}
    /\ writers' = writers \ {a}
    /\ UNCHANGED queue

Next ==
    \/ \E a \in Actors : RequestRead(a)
    \/ \E a \in Actors : RequestWrite(a)
    \/ ProcessQueue
    \/ \E a \in Actors : StopActivity(a)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(ProcessQueue)
    /\ \A a \in Actors : WF_vars(RequestRead(a))
    /\ \A a \in Actors : WF_vars(RequestWrite(a))
    /\ \A a \in Actors : WF_vars(StopActivity(a))

Safety ==
    /\ (writers # {} => readers = {})
    /\ (readers # {} => writers = {})
    /\ Cardinality(writers) =< 1

Liveness ==
    /\ \A a \in Actors : <>(a \in readers)
    /\ \A a \in Actors : <>(a \in writers)
    /\ \A a \in Actors : <>(a \notin readers)
    /\ \A a \in Actors : <>(a \notin writers)

n == NumActors

====