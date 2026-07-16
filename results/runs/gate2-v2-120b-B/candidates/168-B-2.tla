---- MODULE ReadersWriters ----
(*  Fixed version of ReadersWriters.tla  *)

EXTENDS FiniteSets, Naturals, Sequences

CONSTANT NumActors

VARIABLES readers, writers, waiting

(* A tuple representing the whole state, convenient for TLC stuttering *)
vars == <<readers, writers, waiting>>

(* The set of all actor identifiers *)
Actors == 1 .. NumActors

(* ------------------------------------------------------------------------ *)
(*  Helper definitions                                                     *)
(* ------------------------------------------------------------------------ *)

(* Convert a sequence of tuples into a set of those tuples *)
ToSet(s) == { s[i] : i \in DOMAIN s }

(* Predicates for the first component of a queued request *)
read(s)  == s[1] = "read"
write(s) == s[1] = "write"

(* The set of actors waiting to read or write, derived from the waiting queue *)
WaitingToRead  == { p[2] : p \in ToSet(SelectSeq(waiting, read)) }
WaitingToWrite == { p[2] : p \in ToSet(SelectSeq(waiting, write)) }

(* ------------------------------------------------------------------------ *)
(*  Actions                                                                *)
(* ------------------------------------------------------------------------ *)

(* An actor that is not already waiting to read enqueues a read request *)
TryRead(actor) ==
    /\ actor \in Actors
    /\ actor \notin WaitingToRead
    /\ waiting' = Append(waiting, <<"read", actor>>)
    /\ UNCHANGED <<readers, writers>>

(* An actor that is not already waiting to write enqueues a write request *)
TryWrite(actor) ==
    /\ actor \in Actors
    /\ actor \notin WaitingToWrite
    /\ waiting' = Append(waiting, <<"write", actor>>)
    /\ UNCHANGED <<readers, writers>>

(* An actor that is at the head of the queue and requests a read starts reading *)
Read(actor) ==
    /\ readers' = readers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED writers

(* An actor that is at the head of the queue and requests a write starts writing *)
Write(actor) ==
    /\ readers = {}
    /\ writers' = writers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED readers

(* Choose the first queued request (if any) and perform the corresponding action *)
ReadOrWrite ==
    /\ waiting /= <<>>
    /\ writers = {}
    /\ LET pair  == Head(waiting)
           actor == pair[2]
       IN  IF pair[1] = "read"
           THEN Read(actor)
           ELSE Write(actor)

(* An actor currently reading or writing may stop its activity *)
StopActivity(actor) ==
    IF actor \in readers
    THEN /\ readers' = readers \ {actor}
         /\ UNCHANGED <<writers, waiting>>
    ELSE /\ writers' = writers \ {actor}
         /\ UNCHANGED <<readers, waiting>>

(* Stuttering action: at least one active actor stops, or no‑op when none are active *)
Stop ==
    \/ \E actor \in readers : StopActivity(actor)
    \/ \E actor \in writers : StopActivity(actor)
    \/ UNCHANGED <<readers, writers, waiting>>

(* ------------------------------------------------------------------------ *)
(*  Initialization and Next-state relation                                 *)
(* ------------------------------------------------------------------------ *)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ waiting = <<>>

Next ==
    \/ \E actor \in Actors : TryRead(actor)
    \/ \E actor \in Actors : TryWrite(actor)
    \/ ReadOrWrite
    \/ Stop

(* ------------------------------------------------------------------------ *)
(*  Fairness                                                               *)
(* ------------------------------------------------------------------------ *)

Fairness ==
    /\ \A actor \in Actors : WF_vars(TryRead(actor))
    /\ \A actor \in Actors : WF_vars(TryWrite(actor))
    /\ WF_vars(ReadOrWrite)
    /\ WF_vars(Stop)

Spec == Init /\ [][Next]_vars /\ Fairness

(* ------------------------------------------------------------------------ *)
(*  Invariants                                                             *)
(* ------------------------------------------------------------------------ *)

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq({"read", "write"} \times Actors)

Safety ==
    /\ ~(readers # {} /\ writers # {})
    /\ Cardinality(writers) <= 1

(* ------------------------------------------------------------------------ *)
(*  Liveness property (kept unchanged)                                    *)
(* ------------------------------------------------------------------------ *)

Liveness ==
    /\ \A actor \in Actors : []<>(actor \in readers)
    /\ \A actor \in Actors : []<>(actor \in writers)
    /\ \A actor \in Actors : []<>(actor \notin readers)
    /\ \A actor \in Actors : []<>(actor \notin writers)

====