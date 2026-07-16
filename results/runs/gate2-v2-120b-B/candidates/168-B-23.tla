---- MODULE ReadersWriters ----
EXTENDS FiniteSets, Naturals, Sequences

CONSTANT NumActors

VARIABLES readers, writers, waiting

(* Variables bundled for convenience *)
vars == <<readers, writers, waiting>>

(* Set of all actor identifiers *)
Actors == 1..NumActors

(* Helper to convert a sequence to a set of its elements *)
ToSet(s) == { s[i] : i \in DOMAIN s }

(* Predicates distinguishing request types *)
read(s)  == s[1] = "read"
write(s) == s[1] = "write"

(* Queues of waiting readers / writers, extracted from the waiting sequence *)
WaitingToRead  == { p[2] : p \in ToSet(SelectSeq(waiting, read)) }
WaitingToWrite == { p[2] : p \in ToSet(SelectSeq(waiting, write)) }

---------------------------------------------------------------------------
(* Actions *)
---------------------------------------------------------------------------

(* An actor enqueues a read request, if not already waiting to read *)
TryRead(actor) ==
    /\ actor \in Actors
    /\ actor \notin WaitingToRead
    /\ waiting' = Append(waiting, <<"read", actor>>)
    /\ UNCHANGED <<readers, writers>>

(* An actor enqueues a write request, if not already waiting to write *)
TryWrite(actor) ==
    /\ actor \in Actors
    /\ actor \notin WaitingToWrite
    /\ waiting' = Append(waiting, <<"write", actor>>)
    /\ UNCHANGED <<readers, writers>>

(* A queued read request is granted: the actor becomes a reader and
   its request is removed from the front of the queue. *)
Read(actor) ==
    /\ waiting /= <<>>
    /\ Head(waiting)[1] = "read"
    /\ actor = Head(waiting)[2]
    /\ readers' = readers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED writers

(* A queued write request is granted: the actor becomes the sole writer
   and its request is removed from the front of the queue. *)
Write(actor) ==
    /\ waiting /= <<>>
    /\ Head(waiting)[1] = "write"
    /\ actor = Head(waiting)[2]
    /\ readers = {}
    /\ writers' = writers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED readers

(* Choose the request at the front of the queue and dispatch it *)
ReadOrWrite ==
    \/ \E actor \in Actors : Read(actor)
    \/ \E actor \in Actors : Write(actor)

(* An actor that is currently reading or writing stops its activity *)
StopActivity(actor) ==
    IF actor \in readers
    THEN /\ readers' = readers \ {actor}
         /\ UNCHANGED <<writers, waiting>>
    ELSE IF actor \in writers
         THEN /\ writers' = writers \ {actor}
              /\ UNCHANGED <<readers, waiting>>
         ELSE UNCHANGED <<readers, writers, waiting>>

(* Nondeterministically pick any active actor to stop *)
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

(* Type correctness of state variables *)
TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq({"read", "write"} \times Actors)

(* Safety: no simultaneous readers and writers, and at most one writer *)
Safety ==
    /\ ~(readers # {} /\ writers # {})
    /\ Cardinality(writers) <= 1

---------------------------------------------------------------------------
(* Properties *)
---------------------------------------------------------------------------

(* Liveness: each actor eventually reads, eventually writes,
   eventually is not reading, and eventually is not writing. *)
Liveness ==
    /\ \A actor \in Actors : []<>(actor \in readers)
    /\ \A actor \in Actors : []<>(actor \in writers)
    /\ \A actor \in Actors : []<>(actor \notin readers)
    /\ \A actor \in Actors : []<>(actor \notin writers)

=============================================================================