---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

Actors == 0 .. NumActors - 1
Modes == {"read", "write"}

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

QueueMode(i) == queue[i].mode
QueueActor(i) == queue[i].actor

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ queue \in Seq([mode : Modes, actor : Actors])

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = <<>>

RequestRead(a) ==
    /\ \A i \in 1 .. Len(queue) : queue[i].actor # a
    /\ queue' = Append(queue, [mode |-> "read", actor |-> a])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(a) ==
    /\ \A i \in 1 .. Len(queue) : queue[i].actor # a
    /\ queue' = Append(queue, [mode |-> "write", actor |-> a])
    /\ UNCHANGED <<readers, writers>>

BeginReadOrWrite ==
    /\ queue # <<>>
    /\ writers = {}
    /\ LET m == QueueMode(1) IN
        LET a == QueueActor(1) IN
            /\ IF m = "read" THEN readers' = readers \cup {a} ELSE readers' = readers
            /\ IF m = "write" /\ readers = {} THEN writers' = writers \cup {a} ELSE writers' = writers
    /\ queue' = Tail(queue)

StopActivity(a) ==
    /\ readers' = readers \ {a}
    /\ writers' = writers \ {a}
    /\ UNCHANGED queue

Next ==
    \/ \E a \in Actors : RequestRead(a)
    \/ \E a \in Actors : RequestWrite(a)
    \/ BeginReadOrWrite
    \/ \E a \in Actors : StopActivity(a)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E a \in Actors : RequestRead(a))
    /\ WF_vars(\E a \in Actors : RequestWrite(a))
    /\ WF_vars(BeginReadOrWrite)
    /\ WF_vars(\E a \in Actors : StopActivity(a))

Safety ==
    /\ readers \cap writers = {}
    /\ writers \subseteq (Actors \ readers)
    /\ \A a \in Actors : Cardinality(readers \cap {a}) <= 1

Liveness ==
    /\ \A a \in Actors : (a \in readers) ~> (a \notin readers)
    /\ \A a \in Actors : (a \in writers) ~> (a \notin writers)

n == NumActors

====