---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Actors == 1 .. NumActors
Modes == {"read", "write"}
NoMode == "none"

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ queue \in Seq([mode: Modes, who: Actors])

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = <<>>

RequestRead(a) ==
    /\ \A i \in 1 .. Len(queue) : queue[i].who # a
    /\ queue' = Append(queue, [mode |-> "read", who |-> a])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(a) ==
    /\ \A i \in 1 .. Len(queue) : queue[i].who # a
    /\ queue' = Append(queue, [mode |-> "write", who |-> a])
    /\ UNCHANGED <<readers, writers>>

BeginAccess ==
    /\ queue # <<>>
    /\ writers = {}
    /\ LET front == Head(queue) IN
        /\ IF front.mode = "read" THEN
            readers' = readers \cup {front.who}
           ELSE
            /\ readers = {}
            writers' = writers \cup {front.who}
        /\ queue' = Tail(queue)
    /\ UNCHANGED <<readers, writers>>

StopActivity(a) ==
    /\ \/ a \in readers
       \/ a \in writers
    /\ readers' = readers \ {a}
    /\ writers' = writers \ {a}
    /\ UNCHANGED queue

Next ==
    \/ \E a \in Actors : RequestRead(a)
    \/ \E a \in Actors : RequestWrite(a)
    \/ BeginAccess
    \/ \E a \in Actors : StopActivity(a)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E a \in Actors : RequestRead(a))
    /\ WF_vars(\E a \in Actors : RequestWrite(a))
    /\ WF_vars(BeginAccess)
    /\ WF_vars(\E a \in Actors : StopActivity(a))

Safety ==
    /\ (writers # {} => readers = {})
    /\ (readers # {} => writers = {})
    /\ Cardinality(writers) <= 1

Liveness ==
    /\ \A a \in Actors : (a \in readers) ~> (a \notin readers)
    /\ \A a \in Actors : (a \in writers) ~> (a \notin writers)

====