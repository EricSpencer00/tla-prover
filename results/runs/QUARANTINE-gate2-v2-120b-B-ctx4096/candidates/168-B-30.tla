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

\* Helper to turn a sequence into a set of its elements
ToSet(s) == { s[i] : i \in DOMAIN s }

\* Predicate recognising a request record
read(req)  == req[1] = "read"
write(req) == req[1] = "write"

\* Sets of actors that are waiting to read or write
WaitingToRead  == { req[2] : req \in ToSet(waiting) \* select read(req) }
WaitingToWrite == { req[2] : req \in ToSet(waiting) \* select write(req) }

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
    /\ waiting # <<>>                     \* there must be a request to serve
    /\ LET first == Head(waiting) IN
          /\ first[1] = "read"
          /\ first[2] = actor
    /\ readers' = readers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED writers

Write(actor) ==
    /\ waiting # <<>>                     \* there must be a request to serve
    /\ LET first == Head(waiting) IN
          /\ first[1] = "write"
          /\ first[2] = actor
    /\ readers = {}                        \* writers may only proceed when no readers
    /\ writers' = writers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED readers

ReadOrWrite ==
    /\ waiting # <<>>
    /\ writers = {}
    /\ LET first == Head(waiting) IN
          CASE first[1] = "read" -> Read(first[2])
               [] first[1] = "write" -> Write(first[2])

StopActivity(actor) ==
    IF actor \in readers
    THEN /\ readers' = readers \ {actor}
         /\ UNCHANGED <<writers, waiting>>
    ELSE /\ writers' = writers \ {actor}
         /\ UNCHANGED <<readers, waiting>>

Stop ==
    \E actor \in (readers \cup writers) : StopActivity(actor)

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
    /\ ~(readers /= {} /\ writers /= {})
    /\ Cardinality(writers) <= 1

(**************)
(* Properties *)
(**************)

Liveness ==
    /\ \A actor \in Actors : []<>(actor \in readers)
    /\ \A actor \in Actors : []<>(actor \in writers)
    /\ \A actor \in Actors : []<>(actor \notin readers)
    /\ \A actor \in Actors : []<>(actor \notin writers)

=============================================================================