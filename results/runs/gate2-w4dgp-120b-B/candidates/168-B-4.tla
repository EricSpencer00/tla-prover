---- MODULE ReadersWriters ----
EXTENDS FiniteSets, Naturals, Sequences

CONSTANT NumActors

VARIABLES readers, writers, waiting

vars == <<readers, writers, waiting>>

Actors == 1..NumActors

WaitingToRead == { p[2] : p \in { waiting[i] : i \in DOMAIN waiting } /\ p[1] = "read" }
WaitingToWrite == { p[2] : p \in { waiting[i] : i \in DOMAIN waiting } /\ p[1] = "write" }

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ waiting = <<>>

TryRead(actor) ==
    /\ actor \notin WaitingToRead
    /\ waiting' = Append(waiting, <<"read", actor>>)
    /\ UNCHANGED <<readers, writers>>

TryWrite(actor) ==
    /\ actor \notin WaitingToWrite
    /\ waiting' = Append(waiting, <<"write", actor>>)
    /\ UNCHANGED <<readers, writers>>

Read(actor) ==
    /\ waiting # <<>>
    /\ Head(waiting)[1] = "read"
    /\ Head(waiting)[2] = actor
    /\ readers' = readers \union {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED writers

Write(actor) ==
    /\ waiting # <<>>
    /\ Head(waiting)[1] = "write"
    /\ Head(waiting)[2] = actor
    /\ readers = {}
    /\ writers' = writers \union {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED readers

ReadOrWrite == \E actor \in Actors : Read(actor) \/ Write(actor)

StopRead(actor) ==
    /\ actor \in readers
    /\ readers' = readers \ {actor}
    /\ UNCHANGED <<writers, waiting>>

StopWrite(actor) ==
    /\ actor \in writers
    /\ writers' = writers \ {actor}
    /\ UNCHANGED <<readers, waiting>>

Stop == \E actor \in Actors : StopRead(actor) \/ StopWrite(actor)

Next ==
    \/ \E actor \in Actors : TryRead(actor)
    \/ \E actor \in Actors : TryWrite(actor)
    \/ ReadOrWrite
    \/ Stop

Spec == Init /\ [][Next]_vars
    /\ \A actor \in Actors : WF_vars(TryRead(actor))
    /\ \A actor \in Actors : WF_vars(TryWrite(actor))
    /\ WF_vars(ReadOrWrite)
    /\ WF_vars(Stop)

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq({"read", "write"} \times Actors)

Safety ==
    /\ Cardinality(writers) <= 1
    /\ (readers # {} => writers = {})

Liveness ==
    /\ \A a \in Actors : []<>(a \in readers \/ a \in writers)

====