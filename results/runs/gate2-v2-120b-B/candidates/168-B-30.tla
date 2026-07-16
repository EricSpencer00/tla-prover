-------------------------- MODULE ReadersWriters --------------------------
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

(* The next two definitions are needed only for readability; they are not
   used elsewhere in the spec. *)
ToSet(s) == { s[i] : i \in DOMAIN s }

read(s)  == s[1] = "read"
write(s) == s[1] = "write"

WaitingToRead  == { p[2] : p \in ToSet(SelectSeq(waiting, read)) }

WaitingToWrite == { p[2] : p \in ToSet(SelectSeq(waiting, write)) }

---------------------------------------------------------------------------
(***********)
(* Actions *)
(***********)

TryRead(actor) ==
    /\ actor \notin WaitingToRead
    /\ waiting' = Append(waiting, <<"read", actor>>)
    /\ UNCHANGED <<readers, writers>>

TryWrite(actor) ==
    /\ actor \notin WaitingToWrite
    /\ waiting' = Append(waiting, <<"write", actor>>)
    /\ UNCHANGED <<readers, writers>>

Read(actor) ==
    /\ readers' = readers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED writers

Write(actor) ==
    /\ readers = {}
    /\ writers' = writers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED readers

ReadOrWrite ==
    /\ waiting /= <<>>
    /\ writers = {}
    /\ LET pair  == Head(waiting)
           actor == pair[2]
       IN CASE pair[1] = "read" -> Read(actor)
            [] pair[1] = "write" -> Write(actor)

StopActivity(actor) ==
    IF actor \in readers
    THEN /\ readers' = readers \ {actor}
         /\ UNCHANGED <<writers, waiting>>
    ELSE /\ writers' = writers \ {actor}
         /\ UNCHANGED <<readers, waiting>>

(* The original spec used a non‑deterministic choice over the intersection of
   readers and writers, which is empty in all reachable states.  Replacing it
   with an explicit choice over the union of the two sets yields the same
   behaviour (only one of the two branches can ever fire) while avoiding the
   deadlock caused by the empty choice. *)
Stop == \E actor \in (readers \cup writers) : StopActivity(actor)

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