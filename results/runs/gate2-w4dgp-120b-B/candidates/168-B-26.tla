---- MODULE ReadersWriters
(***************************************************************************)
(* Readers-writers with a fairness queue: every request to read or write     *)
(* is enqueued and served in order.  The queued requests can outpace the    *)
(* capacity of the resource, so a bounded-height queue limits how many       *)
(* requests can wait before backpressure blocks further attempts.           *)
(***************************************************************************)
EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS Actors, MaxQueue

VARIABLES readers, writers, waiting

vars == <<readers, writers, waiting>>

WaitingToRead == { p[2] : p \in { waiting[i] : i \in DOMAIN waiting, waiting[i][1] = "read" } }
WaitingToWrite == { p[2] : p \in { waiting[i] : i \in DOMAIN waiting, waiting[i][1] = "write" } }

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq({"read", "write"} \times Actors)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ waiting = <<>>

TryRead(actor) ==
    /\ actor \notin WaitingToRead
    /\ Len(waiting) < MaxQueue
    /\ waiting' = Append(waiting, <<"read", actor>>)
    /\ UNCHANGED <<readers, writers>>

TryWrite(actor) ==
    /\ actor \notin WaitingToWrite
    /\ Len(waiting) < MaxQueue
    /\ waiting' = Append(waiting, <<"write", actor>>)
    /\ UNCHANGED <<readers, writers>>

Read(actor) ==
    /\ readers' = readers \union {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED writers

Write(actor) ==
    /\ readers = {}
    /\ writers' = writers \union {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED readers

ReadOrWrite ==
    /\ waiting /= <<>>
    /\ writers = {}
    /\ LET pair  == Head(waiting)
           actor == pair[2]
       IN IF pair[1] = "read" THEN Read(actor) ELSE Write(actor)

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

Spec ==
    /\ Init /\ [][Next]_vars
    /\ \A actor \in Actors : WF_vars(TryRead(actor))
    /\ \A actor \in Actors : WF_vars(TryWrite(actor))
    /\ WF_vars(ReadOrWrite)
    /\ WF_vars(Stop)

MutualExclusion == ~(readers /= {} /\ writers /= {})
                 /\ Cardinality(writers) <= 1

Liveness ==
    /\ \A actor \in Actors : [](actor \in readers)
    /\ \A actor \in Actors : [](actor \in writers)
    /\ \A actor \in Actors : [](actor \notin readers)
    /\ \A actor \in Actors : [](actor \notin writers)

====