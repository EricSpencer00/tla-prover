---- MODULE ReadersWriters ----
EXTENDS FiniteSets, Naturals, Sequences

CONSTANT NumActors

VARIABLES readers, writers, waiting

vars == <<readers, writers, waiting>>

Actors == 1..NumActors

ToSet(s) == { s[i] : i \in DOMAIN s }

read(s) == s[1] = "read"
write(s) == s[1] = "write"

WaitingToRead ==
    { p[2] : p \in ToSet(SelectSeq(waiting, read)) }

WaitingToWrite ==
    { p[2] : p \in ToSet(SelectSeq(waiting, write)) }

(*-------------------------------------------------------------------*)
(* Actions                                                            *)
(*-------------------------------------------------------------------*)

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
    /\ waiting[1][2] = actor
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
    \/ /\ waiting /= <<>>
       /\ waiting[1][1] = "read"
       /\ Read(waiting[1][2])
    \/ /\ waiting /= <<>>
       /\ waiting[1][1] = "write"
       /\ Write(waiting[1][2])

StopActivity(actor) ==
    IF actor \in readers
    THEN /\ readers' = readers \ {actor}
         /\ UNCHANGED <<writers, waiting>>
    ELSE /\ writers' = writers \ {actor}
         /\ UNCHANGED <<readers, waiting>>

Stop == \E actor \in (readers \cup writers) : StopActivity(actor)

(*-------------------------------------------------------------------*)
(* Specification                                                      *)
(*-------------------------------------------------------------------*)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ waiting = <<>>

Next ==
    \/ \E actor \in Actors : TryRead(actor)
    \/ \E actor \in Actors : TryWrite(actor)
    \/ ReadOrWrite
    \/ Stop

Spec == Init /\ [][Next]_vars

(*-------------------------------------------------------------------*)
(* Invariants                                                         *)
(*-------------------------------------------------------------------*)

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq({"read", "write"} \times Actors)

Safety ==
    /\ ~(readers # {} /\ writers # {})
    /\ Cardinality(writers) <= 1

=============================================================================