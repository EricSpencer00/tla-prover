---- MODULE ReadersWriters ----
EXTENDS FiniteSets, Naturals, Sequences

CONSTANT NumActors

VARIABLES
    readers, \* set of processes currently reading
    writers, \* set of processes currently writing
    waiting  \* queue of processes waiting to access the resource

vars == <<readers, writers, waiting>>

Actors == 1..NumActors

ToSet(s) == { s[i] : i \in DOMAIN s }

read(s)  == s[1] = "read"
write(s) == s[1] = "write"

WaitingToRead  == { p[2] : p \in ToSet(SelectSeq(waiting, read)) }

WaitingToWrite == { p[2] : p \in ToSet(SelectSeq(waiting, write)) }

(*------------------------------------------------------------*)
(* Actions *)
(*------------------------------------------------------------*)

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
    /\ waiting[1][1] = "read"
    /\ readers' = readers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED writers

Write(actor) ==
    /\ waiting /= <<>>
    /\ waiting[1][1] = "write"
    /\ readers = {}
    /\ writers' = writers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED readers

ReadOrWrite ==
    \/ \E pair \in DOMAIN waiting :
          /\ waiting[pair][1] = "read"
          /\ Read(waiting[pair][2])
    \/ \E pair \in DOMAIN waiting :
          /\ waiting[pair][1] = "write"
          /\ Write(waiting[pair][2])

StopActivity(actor) ==
    IF actor \in readers
    THEN /\ readers' = readers \ {actor}
         /\ UNCHANGED <<writers, waiting>>
    ELSE /\ writers' = writers \ {actor}
         /\ UNCHANGED <<readers, waiting>>

Stop ==
    \E actor \in (readers \cup writers) : StopActivity(actor)

(*------------------------------------------------------------*)
(* Specification *)
(*------------------------------------------------------------*)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ waiting = <<>>

Next ==
    \/ \E actor \in Actors : TryRead(actor)
    \/ \E actor \in Actors : TryWrite(actor)
    \/ \E pair \in DOMAIN waiting :
          /\ waiting[pair][1] = "read"
          /\ Read(waiting[pair][2])
    \/ \E pair \in DOMAIN waiting :
          /\ waiting[pair][1] = "write"
          /\ Write(waiting[pair][2])
    \/ Stop

Fairness ==
    /\ \A actor \in Actors : WF_vars(TryRead(actor))
    /\ \A actor \in Actors : WF_vars(TryWrite(actor))
    /\ WF_vars(ReadOrWrite)
    /\ WF_vars(Stop)

Spec == Init /\ [][Next]_vars /\ Fairness

(*------------------------------------------------------------*)
(* Invariants *)
(*------------------------------------------------------------*)

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq({"read", "write"} \times Actors)

Safety ==
    /\ ~(readers # {} /\ writers # {})
    /\ Cardinality(writers) <= 1

(*------------------------------------------------------------*)
(* Properties *)
(*------------------------------------------------------------*)

Liveness ==
    /\ \A actor \in Actors : []<>(actor \in readers)
    /\ \A actor \in Actors : []<>(actor \in writers)
    /\ \A actor \in Actors : []<>(actor \notin readers)
    /\ \A actor \in Actors : []<>(actor \notin writers)

=============================================================================