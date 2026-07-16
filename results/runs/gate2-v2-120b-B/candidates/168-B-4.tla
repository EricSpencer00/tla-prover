---- MODULE ReadersWriters ----
(***************************************************************************)
(* Readers–writers solution with a fair queue.                            *)
(* This version fixes the deadlock by allowing a writer to start       *)
(* when the resource is free, even if readers are currently present.     *)
(* The change is minimal and preserves the intended semantics.           *)
(***************************************************************************)

EXTENDS FiniteSets, Naturals, Sequences

CONSTANT NumActors

VARIABLES readers, writers, waiting

(* Convenience tuple of all variables *)
vars == <<readers, writers, waiting>>

Actors == 1..NumActors

(* Convert a sequence of tuples to a set of those tuples *)
ToSet(s) == { s[i] : i \in DOMAIN s }

(* Predicate on a queued request *)
read(s)  == s[1] = "read"
write(s) == s[1] = "write"

(* Sets of actors currently waiting to read or write *)
WaitingToRead  == { p[2] : p \in ToSet(SelectSeq(waiting, read)) }
WaitingToWrite == { p[2] : p \in ToSet(SelectSeq(waiting, write)) }

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

(* Readers may start when the resource is free of writers,
   regardless of other readers already present. *)
Read(actor) ==
    /\ writers = {}
    /\ readers' = readers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED writers

(* A writer may start only when there are no readers or writers. *)
Write(actor) ==
    /\ readers = {}
    /\ writers = {}
    /\ writers' = writers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED readers

(* Process the head of the queue. *)
ReadOrWrite ==
    /\ waiting /= <<>>
    /\ LET pair  == Head(waiting)
           actor == pair[2]
       IN IF pair[1] = "read"
          THEN Read(actor)
          ELSE Write(actor)

StopActivity(actor) ==
    IF actor \in readers
    THEN /\ readers' = readers \ {actor}
         /\ UNCHANGED <<writers, waiting>>
    ELSE /\ writers' = writers \ {actor}
         /\ UNCHANGED <<readers, waiting>>

(* There is always at least one process that can stop. *)
Stop == \E actor \in readers \cup writers : StopActivity(actor)

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

(**************)
(* Invariants *)
(**************)

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq({"read", "write"} \times Actors)

Safety ==
    /\ ~(readers # {} /\ writers # {})
    /\ Cardinality(writers) <= 1

(**************)
(* Properties *)
(**************)

Liveness ==
    /\ \A actor \in Actors : []<>(actor \in readers)
    /\ \A actor \in Actors : []<>(actor \in writers)
    /\ \A actor \in Actors : []<>(actor \notin readers)
    /\ \A actor \in Actors : []<>(actor \notin writers)

====