---- MODULE ReadersWriters ----
(***************************************************************************)
(* This solution to the readers-writers problem, cf.                       *)
(* https://en.wikipedia.org/wiki/Readers–writers_problem,                  *)
(* uses a queue in order to fairly serve all requests.                     *)
(***************************************************************************)
EXTENDS FiniteSets, Naturals, Sequences

CONSTANT NumActors

VARIABLES
    readers, \* set of processes currently reading
    writers, \* set of processes currently writing
    waiting  \* queue of processes waiting to access the resource

vars == <<readers, writers, waiting>>

Actors == 1..NumActors

(* --------------------------------------------------------------------- *)
(* Helper definitions to extract the waiting queue as a set of pairs    *)
(* --------------------------------------------------------------------- *)

WaitingSet == { waiting[i] : i \in DOMAIN waiting }

WaitingToRead  == { p[2] : p \in WaitingSet /\ p[1] = "read" }

WaitingToWrite == { p[2] : p \in WaitingSet /\ p[1] = "write" }

---------------------------------------------------------------------------
(* Actions *)
---------------------------------------------------------------------------

TryRead(actor) ==
    /\ actor \notin WaitingToRead
    /\ waiting' = Append(waiting, <<"read", actor>>)
    /\ UNCHANGED <<readers, writers>>

TryWrite(actor) ==
    /\ actor \notin WaitingToWrite
    /\ waiting' = Append(waiting, <<"write", actor>>)
    /\ UNCHANGED <<readers, writers>>

Read(actor) ==
    /\ waiting /= <<>>
    /\ Head(waiting)[1] = "read"
    /\ Head(waiting)[2] = actor
    /\ readers' = readers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED writers

Write(actor) ==
    /\ waiting /= <<>>
    /\ Head(waiting)[1] = "write"
    /\ Head(waiting)[2] = actor
    /\ readers = {}
    /\ writers' = writers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED readers

ReadOrWrite ==
    \/ \E actor \in Actors : Read(actor)
    \/ \E actor \in Actors : Write(actor)

StopActivity(actor) ==
    IF actor \in readers
    THEN /\ readers' = readers \ {actor}
         /\ UNCHANGED <<writers, waiting>>
    ELSE /\ writers' = writers \ {actor}
         /\ UNCHANGED <<readers, waiting>>

Stop == \E actor \in (readers \cup writers) : StopActivity(actor)

---------------------------------------------------------------------------
(* Specification *)
---------------------------------------------------------------------------

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ waiting = <<>>

Next ==
    \/ \E actor \in Actors : TryRead(actor)
    \/ \E actor \in Actors : TryWrite(actor)
    \/ ReadOrWrite
    \/ Stop

Fairness ==
    /\ \A actor \in Actors : WF_vars(TryRead(actor))
    /\ \A actor \in Actors : WF_vars(TryWrite(actor))
    /\ WF_vars(ReadOrWrite)
    /\ WF_vars(Stop)

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Invariants *)
---------------------------------------------------------------------------

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq({"read", "write"} \times Actors)

Safety ==
    /\ ~(readers # {} /\ writers # {})
    /\ Cardinality(writers) <= 1

---------------------------------------------------------------------------
(* Properties *)
---------------------------------------------------------------------------

Liveness ==
    /\ \A actor \in Actors : []<>(actor \in readers)
    /\ \A actor \in Actors : []<>(actor \in writers)
    /\ \A actor \in Actors : []<>(actor \notin readers)
    /\ \A actor \in Actors : []<>(actor \notin writers)

=============================================================================