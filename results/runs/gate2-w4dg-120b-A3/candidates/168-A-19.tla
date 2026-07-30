---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

Reqs == {"read", "write"}
Actors == 0 .. (NumActors - 1)

Req == [who : Actors, kind : Reqs]

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ queue \in Seq(Reqs \cup Actors)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = <<>>

RequestRead(p) ==
    /\ p \notin readers
    /\ p \notin writers
    /\ queue' = Append(queue, [who |-> p, kind |-> "read"])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
    /\ p \notin readers
    /\ p \notin writers
    /\ queue' = Append(queue, [who |-> p, kind |-> "write"])
    /\ UNCHANGED <<readers, writers>>

BeginReadOrWrite ==
    /\ queue # <<>>
    /\ writers = {}
    /\ LET m == Head(queue) IN
        /\ IF m.kind = "read"
           THEN readers' = readers \cup {m.who}
           ELSE /\ writers' = writers \cup {m.who}
                /\ readers' = readers
        /\ queue' = Tail(queue)

StopActivity(p) ==
    /\ \/ p \in readers
       \/ p \in writers
    /\ readers' = readers \ {p}
    /\ writers' = writers \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in Actors : RequestRead(p)
    \/ \E p \in Actors : RequestWrite(p)
    \/ BeginReadOrWrite
    \/ \E p \in Actors : StopActivity(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in Actors : RequestRead(p))
    /\ WF_vars(\E p \in Actors : RequestWrite(p))
    /\ WF_vars(BeginReadOrWrite)
    /\ WF_vars(\E p \in Actors : StopActivity(p))

Safety ==
    /\ readers \cap writers = {}
    /\ Cardinality(writers) <= 1

Liveness ==
    /\ \A p \in Actors : (p \in readers) ~> (p \notin readers)
    /\ \A p \in Actors : (p \in writers) ~> (p \notin writers)
    /\ \A p \in Actors : (p \notin readers) ~> (p \in readers)
    /\ \A p \in Actors : (p \notin writers) ~> (p \in writers)

n == NumActors

====