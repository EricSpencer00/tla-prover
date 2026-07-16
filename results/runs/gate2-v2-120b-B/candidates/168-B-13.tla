---- MODULE ReadersWriters ----
EXTENDS FiniteSets, Naturals, Sequences

CONSTANT NumActors

VARIABLES
    readers,   \* set of processes currently reading
    writers,   \* set of processes currently writing
    waiting    \* queue of processes waiting to access the resource

vars == <<readers, writers, waiting>>

Actors == 1..NumActors

(* Helper to convert a sequence of pairs into a set of the pairs *)
ToSet(s) == { s[i] : i \in DOMAIN s }

read(s)  == s[1] = "read"
write(s) == s[1] = "write"

(* Subset of the waiting queue that are read requests, projected to the actor *)
WaitingToRead  == { p[2] : p \in ToSet(SelectSeq(waiting, read)) }

(* Subset of the waiting queue that are write requests, projected to the actor *)
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
       IN IF pair[1] = "read"
          THEN Read(actor)
          ELSE Write(actor)

StopActivity(actor) ==
    IF actor \in readers
    THEN /\ readers' = readers \ {actor}
         /\ UNCHANGED <<writers, waiting>>
    ELSE /\ writers' = writers \ {actor}
         /\ UNCHANGED <<readers, waiting>>

(* The stop action is enabled when at least one actor is either reading or writing *)
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

(* Weak fairness for each action that can change the state *)
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