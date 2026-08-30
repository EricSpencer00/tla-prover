---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

Requests == [actor : 1..NumActors, mode : {"read", "write"}]

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

TypeOK ==
    /\ readers \subseteq (1..NumActors)
    /\ writers \subseteq (1..NumActors)
    /\ queue \in Seq(Requests)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = <<>>

RequestRead(a) ==
    /\ ~ \E i \in DOMAIN queue : queue[i].actor = a /\ queue[i].mode = "read"
    /\ queue' = Append(queue, [actor |-> a, mode |-> "read"])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(a) ==
    /\ ~ \E i \in DOMAIN queue : queue[i].actor = a /\ queue[i].mode = "write"
    /\ queue' = Append(queue, [actor |-> a, mode |-> "write"])
    /\ UNCHANGED <<readers, writers>>

BeginAccess ==
    /\ queue # <<>>
    /\ writers = {}
    /\ LET r == Head(queue) IN
        /\ IF r.mode = "read" THEN readers' = readers \cup {r.actor} ELSE readers' = readers
        /\ IF r.mode = "write" /\ readers = {} THEN writers' = writers \cup {r.actor} ELSE writers' = writers
        /\ queue' = Tail(queue)

StopActivity(a) ==
    /\ readers \cup writers # {}
    /\ readers' = readers \ {a}
    /\ writers' = writers \ {a}
    /\ UNCHANGED queue

Next ==
    \/ \E a \in 1..NumActors : RequestRead(a)
    \/ \E a \in 1..NumActors : RequestWrite(a)
    \/ BeginAccess
    \/ \E a \in 1..NumActors : StopActivity(a)

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(\E a \in 1..NumActors : RequestRead(a))
    /\ WF_vars(\E a \in 1..NumActors : RequestWrite(a))
    /\ WF_vars(BeginAccess)
    /\ \A a \in 1..NumActors : SF_vars(StopActivity(a))

Safety ==
    /\ (writers # {} => readers = {})
    /\ (readers # {} => writers = {})
    /\ writers \subseteq (1..NumActors)
    /\ readers \subseteq (1..NumActors)

Liveness ==
    /\ \A a \in 1..NumActors :
         /\ (a \in readers) ~> (a \notin readers)
         /\ (a \in writers) ~> (a \notin writers)
    /\ \A a \in 1..NumActors : (a \in readers) ~> (a \in writers)
    /\ \A a \in 1..NumActors : (a \in writers) ~> (a \in readers)

n == NumActors

====