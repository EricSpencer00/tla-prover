---- MODULE ReadersWriters_corrected ----
EXTENDS FiniteSets, Naturals, Sequences

CONSTANT NumActors

VARIABLES readers, writers, waiting

vars == <<readers, writers, waiting>>

Actors == 1..NumActors

(* Helper for converting a sequence to a set of its elements *)
SeqToSet(s) == { s[i] : i \in DOMAIN s }

(* Predicate to recognise a request tuple *)
IsRead(t)  == t[1] = "read"
IsWrite(t) == t[1] = "write"

(* Subsets of actors currently waiting for the resource *)
WaitingToRead  == { t[2] : t \in SeqToSet(waiting) /\ IsRead(t) }
WaitingToWrite == { t[2] : t \in SeqToSet(waiting) /\ IsWrite(t) }

(***************************************************************************)
(* Actions                                                               *)
(***************************************************************************)

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
    /\ actors[1][2] = actor
    /\ readers' = readers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED writers

Write(actor) ==
    /\ waiting /= <<>>
    /\ waiting[1][1] = "write"
    /\ waiting[1][2] = actor
    /\ readers = {}
    /\ writers' = writers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED readers

ReadOrWrite ==
    /\ waiting /= <<>>
    /\ writers = {}
    LET pair == Head(waiting) IN
        IF pair[1] = "read"
        THEN Read(pair[2])
        ELSE Write(pair[2])

StopActivity(actor) ==
    IF actor \in readers
    THEN /\ readers' = readers \ {actor}
         /\ UNCHANGED <<writers, waiting>>
    ELSE /\ writers' = writers \ {actor}
         /\ UNCHANGED <<readers, waiting>>

Stop == \E actor \in (readers \cup writers) : StopActivity(actor)

(***************************************************************************)
(* Specification                                                         *)
(***************************************************************************)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ waiting = <<>>

Next ==
    \/ \E actor \in Actors : TryRead(actor)
    \/ \E actor \in Actors : TryWrite(actor)
    \/ ReadOrWrite
    \/ Stop

(* Weak fairness for each individual action *)
Fairness ==
    /\ \A actor \in Actors : WF_vars(TryRead(actor))
    /\ \A actor \in Actors : WF_vars(TryWrite(actor))
    /\ WF_vars(ReadOrWrite)
    /\ WF_vars(Stop)

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Invariants                                                            *)
(***************************************************************************)

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq({"read", "write"} \times Actors)

Safety ==
    /\ ~(readers # {} /\ writers # {})
    /\ Cardinality(writers) <= 1

(***************************************************************************)
(* (Optional) Liveness property – kept for completeness but not used     *)
(***************************************************************************)

Liveness ==
    /\ \A actor \in Actors : []<>(actor \in readers)
    /\ \A actor \in Actors : []<>(actor \in writers)
    /\ \A actor \in Actors : []<>(actor \notin readers)
    /\ \A actor \in Actors : []<>(actor \notin writers)

====