---- MODULE ReadersWriters ----
EXTENDS FiniteSets, Naturals, Sequences

CONSTANT NumActors

VARIABLES readers, writers, waiting
vars == <<readers, writers, waiting>>

Actors == 1..NumActors
ToSet(s) == { s[i] : i \in DOMAIN s }
Read(s)  == s[1] = "read"
Write(s) == s[1] = "write"
WaitingToRead  == { p[2] : p \in ToSet(SelectSeq(waiting, Read)) }
WaitingToWrite == { p[2] : p \in ToSet(SelectSeq(waiting, Write)) }

TryRead(a) ==
    /\ a \notin WaitingToRead
    /\ waiting' = Append(waiting, <<"read", a>>)
    /\ UNCHANGED <<readers, writers>>

TryWrite(a) ==
    /\ a \notin WaitingToWrite
    /\ waiting' = Append(waiting, <<"write", a>>)
    /\ UNCHANGED <<readers, writers>>

Read(a) ==
    /\ readers' = readers \union {a}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED writers

Write(a) ==
    /\ readers = {}
    /\ writers' = writers \union {a}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED readers

ReadOrWrite ==
    /\ waiting # <<>>
    /\ writers = {}
    /\ LET p == Head(waiting)
           a == p[2]
       IN CASE p[1] = "read" -> Read(a)
            [] p[1] = "write" -> Write(a)

StopActivity(a) ==
    IF a \in readers
    THEN readers' = readers \ {a}
    ELSE writers' = writers \ {a}
    /\ UNCHANGED waiting

Stop == \E a \in readers \cap writers : StopActivity(a)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ waiting = <<>>

Next ==
    \/ \E a \in Actors : TryRead(a)
    \/ \E a \in Actors : TryWrite(a)
    \/ ReadOrWrite
    \/ Stop

Spec ==
    /\ Init /\ [][Next]_vars
    /\ \A a \in Actors : WF_vars(TryRead(a))
    /\ \A a \in Actors : WF_vars(TryWrite(a))
    /\ WF_vars(ReadOrWrite)
    /\ WF_vars(Stop)

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq({"read", "write"} \times Actors)

Safety ==
    /\ ~(readers # {} /\ writers # {})
    /\ Cardinality(writers) <= 1

Liveness ==
    /\ \A a \in Actors : []<>(a \in readers)
    /\ \A a \in Actors : []<>(a \in writers)
    /\ \A a \in Actors : []<>(a \notin readers)
    /\ \A a \in Actors : []<>(a \notin writers)

====