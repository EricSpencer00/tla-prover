---- MODULE ReadersWriters
(***************************************************************************)
(* Readers-writers solution with a queue for fairness.                     *)
(* A process first queues a request, then reads or writes only when it is *)
(* at the head; a writer needs exclusive access, a reader needs no writer. *)
(***************************************************************************)
EXTENDS FiniteSets, Naturals, Sequences

CONSTANT NumActors

VARIABLES readers, writers, waiting
vars == <<readers, writers, waiting>>
Actors == 1..NumActors

WaitingToRead == { p[2] : p \in { w \in SetElems(waiting) : Head(w) = "read" } }
WaitingToWrite == { p[2] : p \in { w \in SetElems(waiting) : Head(w) = "write" } }

TryRead(a) ==
    /\ a \notin WaitingToRead
    /\ waiting' = Append(waiting, <<"read", a>>)
    /\ UNCHANGED <<readers, writers>>

TryWrite(a) ==
    /\ a \notin WaitingToWrite
    /\ waiting' = Append(waiting, <<"write", a>>)
    /\ UNCHANGED <<readers, writers>>

Read(a) ==
    /\ Head(waiting)[2] = a
    /\ readers' = readers \union {a}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED writers

Write(a) ==
    /\ writers = {}
    /\ Head(waiting)[2] = a
    /\ writers' = writers \union {a}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED readers

StopActivity(a) ==
    /\ \/ /\ a \in readers
          /\ readers' = readers \ {a}
          /\ UNCHANGED writers
       \/ /\ a \in writers
          /\ writers' = writers \ {a}
          /\ UNCHANGED readers
    /\ UNCHANGED waiting

Next ==
    \/ \E a \in Actors : TryRead(a)
    \/ \E a \in Actors : TryWrite(a)
    \/ \E a \in Actors : Read(a)
    \/ \E a \in Actors : Write(a)
    \/ \E a \in Actors : StopActivity(a)

Spec == Init /\ [][Next]_vars
Init == readers = {} /\ writers = {} /\ waiting = <<>>

TypeOK ==
    /\ readers \subseteq Actors /\ writers \subseteq Actors
    /\ waiting \in Seq({"read","write"} \times Actors)

Safety ==
    /\ writers = {} \/ readers = {}
    /\ Cardinality(writers) <= 1

Liveness ==
    /\ \A a \in Actors : []<>(a \in readers)
    /\ \A a \in Actors : []<>(a \in writers)
    /\ \A a \in Actors : []<>(a \notin readers)
    /\ \A a \in Actors : []<>(a \notin writers)

====