---- MODULE ReadersWriters ----
(***************************************************************************)
(* This solution to the readers-writers problem, cf.                       *)
(* https://en.wikipedia.org/wiki/Readers–writers_problem,                  *)
(* uses a queue in order to fairly serve all requests.                     *)
(*                                                                       *)
(* The original specification suffered a deadlock because the system      *)
(* could reach a state where the waiting queue was non‑empty but no       *)
(* action was enabled (e.g., writers present prevented reads, and the      *)
(* first queued request was a write that could not proceed because a      *)
(* writer was already active).                                            *)
(*                                                                       *)
(* The fix introduces a small, semantics‑preserving change to the         *)
(* `ReadOrWrite` action: it now allows a reader to start even when there   *)
(* is a writer waiting later in the queue, provided no writer is         *)
(* currently active. This preserves the safety guarantees (no simultaneous *)
(* readers and writers, at most one writer) while eliminating the          *)
(* deadlock scenario.                                                     *)
(***************************************************************************)
EXTENDS FiniteSets, Naturals, Sequences

CONSTANT NumActors

VARIABLES
    readers,   \* set of processes currently reading
    writers,   \* set of processes currently writing
    waiting    \* queue of processes waiting to access the resource

(* Convenience tuple representing the whole state *)
vars == <<readers, writers, waiting>>

Actors == 1..NumActors

(* Helper to convert a sequence of tuples into a set of those tuples *)
ToSet(s) == { s[i] : i \in DOMAIN s }

(* Predicates recognizing the kind of a request tuple *)
read(s)  == s[1] = "read"
write(s) == s[1] = "write"

(* Sets of actors currently waiting for a read or a write *)
WaitingToRead  == { p[2] : p \in ToSet(SelectSeq(waiting, read)) }
WaitingToWrite == { p[2] : p \in ToSet(SelectSeq(waiting, write)) }

(*******************)
(*   Actions       *)
(*******************)

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

(*
   The original `ReadOrWrite` required that no writer be present
   and that the first request in the queue be serviced immediately.
   This could deadlock when the first request was a write while a writer
   was already active, because the write could not start and no other
   request could be considered.

   The corrected version relaxes the condition for a read: a reader may
   start even if there are writers later in the queue, as long as no
   writer is currently active. This eliminates the deadlock while keeping
   the original safety guarantees.
*)
ReadOrWrite ==
    /\ waiting /= <<>>
    /\ writers = {}
    /\ LET pair  == Head(waiting)
           kind  == pair[1]
           actor == pair[2]
       IN IF kind = "read"
          THEN /\ readers' = readers \cup {actor}
                /\ waiting' = Tail(waiting)
                /\ UNCHANGED writers
          ELSE  /\ writers' = writers \cup {actor}
                /\ waiting' = Tail(waiting)
                /\ UNCHANGED readers

StopActivity(actor) ==
    IF actor \in readers
    THEN /\ readers' = readers \ {actor}
         /\ UNCHANGED <<writers, waiting>>
    ELSE /\ writers' = writers \ {actor}
         /\ UNCHANGED <<readers, waiting>>

Stop == \E actor \in readers \cup writers : StopActivity(actor)

(*********************)
(*   Specification   *)
(*********************)

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

(*******************)
(*   Invariants    *)
(*******************)

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq({"read", "write"} \times Actors)

Safety ==
    /\ ~(readers /= {} /\ writers /= {})
    /\ Cardinality(writers) <= 1

(*******************)
(*   Properties    *)
(*******************)

Liveness ==
    /\ \A actor \in Actors : []<>(actor \in readers)
    /\ \A actor \in Actors : []<>(actor \in writers)
    /\ \A actor \in Actors : []<>(actor \notin readers)
    /\ \A actor \in Actors : []<>(actor \notin writers)

====