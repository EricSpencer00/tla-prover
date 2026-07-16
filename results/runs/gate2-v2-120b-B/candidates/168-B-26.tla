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

(* Helper to extract a set of elements from a sequence *)
ToSet(s) == { s[i] : i \in DOMAIN s }

(* Predicate that checks the first component of a pair *)
read(s)  == s[1] = "read"
write(s) == s[1] = "write"

(* Sets of actors currently waiting to read or write *)
WaitingToRead  == { p[2] : p \in ToSet(SelectSeq(waiting, read)) }

WaitingToWrite == { p[2] : p \in ToSet(SelectSeq(waiting, write)) }

---------------------------------------------------------------------------
(***********)
(* Actions *)
(***********)

(* A process that is not already waiting to read adds a read request to the tail of the queue *)
TryRead(actor) ==
    /\ actor \notin WaitingToRead
    /\ waiting' = Append(waiting, <<"read", actor>>)
    /\ UNCHANGED <<readers, writers>>

(* A process that is not already waiting to write adds a write request to the tail of the queue *)
TryWrite(actor) ==
    /\ actor \notin WaitingToWrite
    /\ waiting' = Append(waiting, <<"write", actor>>)
    /\ UNCHANGED <<readers, writers>>

(* The head of the queue is a read request; the actor starts reading and the request is removed *)
Read(actor) ==
    /\ readers' = readers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED writers

(* The head of the queue is a write request and no one is reading; the actor starts writing and the request is removed *)
Write(actor) ==
    /\ readers = {}
    /\ writers' = writers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED readers

(* Choose the first request in the queue (if any) and perform it. *)
ReadOrWrite ==
    /\ waiting /= <<>>
    /\ writers = {}
    /\ LET pair  == Head(waiting)
           actor == pair[2]
       IN IF pair[1] = "read"
          THEN Read(actor)
          ELSE Write(actor)

(* A process that is currently reading or writing may stop; the waiting queue is unchanged *)
StopActivity(actor) ==
    IF actor \in readers
    THEN /\ readers' = readers \ {actor}
         /\ UNCHANGED <<writers, waiting>>
    ELSE /\ writers' = writers \ {actor}
         /\ UNCHANGED <<readers, waiting>>

(* There is always at least one process that can stop when both readers and writers are non‑empty,
   which prevents deadlock in that situation. *)
Stop == \E actor \in readers \cup writers : StopActivity(actor)

---------------------------------------------------------------------------
(*****************)
(* Specification *)
(*****************)

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
(**************)
(* Invariants *)
(**************)

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq({"read", "write"} \times Actors)

Safety ==
    /\ ~(readers /= {} /\ writers /= {})          \* No simultaneous readers and writers
    /\ Cardinality(writers) <= 1                  \* At most one writer

(**************)
(* Properties *)
(**************)

Liveness ==
    /\ \A actor \in Actors : []<>(actor \in readers)
    /\ \A actor \in Actors : []<>(actor \in writers)
    /\ \A actor \in Actors : []<>(actor \notin readers)
    /\ \A actor \in Actors : []<>(actor \notin writers)

====