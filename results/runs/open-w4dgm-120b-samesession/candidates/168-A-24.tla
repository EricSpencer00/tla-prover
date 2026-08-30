---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Actor == 1..NumActors

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

QueueItem == [actor : Actor, kind : {"read", "write"}]

TypeOK ==
    /\ readers \subseteq Actor
    /\ writers \subseteq Actor
    /\ queue \in Seq(QueueItem)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = << >>

RequestRead(a) ==
    \/ \A i \in 1..Len(queue) : ~(queue[i].actor = a /\ queue[i].kind = "read")
    /\ queue' = Append(queue, [actor |-> a, kind |-> "read"])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(a) ==
    /\ \A i \in 1..Len(queue) : ~(queue[i].actor = a /\ queue[i].kind = "write")
    /\ queue' = Append(queue, [actor |-> a, kind |-> "write"])
    /\ UNCHANGED <<readers, writers>>

Begin ==
    /\ queue # << >>
    /\ writers = {}
    /\ LET item == Head(queue) IN
        /\ \/ (item.kind = "read" /\ readers' = readers \cup {item.actor})
           \/ (item.kind = "write" /\ readers = {} /\ writers' = writers \cup {item.actor})
        /\ queue' = Tail(queue)
    /\ UNCHANGED <<writers, readers>>

StopActivity(a) ==
    \/ readers' = readers \ {a}
    \/ writers' = writers \ {a}
    /\ UNCHANGED queue

Next ==
    \/ \E a \in Actor : RequestRead(a) \/ RequestWrite(a) \/ StopActivity(a)
    \/ Begin

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(Next)

Safety ==
    /\ readers # {} => writers = {}
    /\ readers \cap writers = {}
    /\ \A a1 \in writers, a2 \in writers : a1 = a2
    /\ Cardinality(writers) <= 1

Liveness ==
    /\ \A a \in Actor : (a \notin readers) ~> (a \in readers)
    /\ \A a \in Actor : (a \notin writers) ~> (a \in writers)
    /\ \A a \in Actor : (a \in readers) ~> (a \notin readers)
    /\ \A a \in Actor : (a \in writers) ~> (a \notin writers)

n == NumActors
====