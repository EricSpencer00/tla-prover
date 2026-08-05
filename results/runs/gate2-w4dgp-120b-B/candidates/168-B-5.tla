---- MODULE ReadersWriters ----
(* This solution to the readers-writers problem (cf. https://en.wikipedia.org/wiki/Readers%E2%80%93writers_problem)
   uses a queue to fairly serve all requests. *)
EXTENDS FiniteSets, Naturals, Sequences

CONSTANT NumActors

VARIABLES readers, writers, waiting
vars == <<readers, writers, waiting>>

Actors == 1..NumActors
ToSet(s) == { s[i] : i \in DOMAIN s }
read(s)  == s[1] = "read"
write(s) == s[1] = "write"
WaitingToRead  == { p[2] : p \in ToSet(SelectSeq(waiting, read)) }
WaitingToWrite == { p[2] : p \in ToSet(SelectSeq(waiting, write)) }

TryRead( a ) ==
    /\ a \notin WaitingToRead
    /\ waiting' = Append(waiting, <<"read", a>>)
    /\ UNCHANGED <<readers, writers>>

TryWrite( a ) ==
    /\ a \notin WaitingToWrite
    /\ waiting' = Append(waiting, <<"write", a>>)
    /\ UNCHANGED <<readers, writers>>

Read( a ) ==
    /\ readers' = readers \union {a}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED writers

Write( a ) ==
    /\ readers = {}
    /\ writers' = writers \union {a}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED readers

ReadOrWrite ==
    /\ waiting /= <<>>
    /\ writers = {}
    /\ LET p == Head(waiting) IN
         IF p[1] = "read"
         THEN Read(p[2])
         ELSE Write(p[2])

StopActivity( a ) ==
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
    \/ \E a \in Actors : TryRead(a) \/ TryWrite(a)
    \/ ReadOrWrite \/ Stop

Fairness ==
    /\ \A a \in Actors : WF_vars(TryRead(a)) /\ WF_vars(TryWrite(a))
    /\ WF_vars(ReadOrWrite) /\ WF_vars(Stop)

Spec == Init /\ [][Next]_vars /\ Fairness

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