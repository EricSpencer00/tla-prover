---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

(* Set of processes *)
n == 1..NumActors
Proc == n

(* Request record *)
Req == [proc: Proc, type: {"read","write"}]

VARIABLES readers, writers, queue

(* Initial state *)
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = <<>>

(* Type correctness invariant *)
TypeOK ==
    /\ readers \subseteq Proc
    /\ writers \subseteq Proc
    /\ readers \cap writers = {}
    /\ Cardinality(writers) <= 1
    /\ queue \in Seq(Req)

(* Safety invariant *)
Safety ==
    /\ (readers = {} \/ writers = {})
    /\ Cardinality(writers) <= 1

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

(* A process requests read access *)
RequestRead ==
    \E p \in Proc :
        /\ p \notin readers
        /\ p \notin writers
        /\ \A i \in 1..Len(queue) : queue[i].proc # p
        /\ readers' = readers
        /\ writers' = writers
        /\ queue'   = Append(queue, [proc |-> p, type |-> "read"])

(* A process requests write access *)
RequestWrite ==
    \E p \in Proc :
        /\ p \notin readers
        /\ p \notin writers
        /\ \A i \in 1..Len(queue) : queue[i].proc # p
        /\ readers' = readers
        /\ writers' = writers
        /\ queue'   = Append(queue, [proc |-> p, type |-> "write"])

(* The front of the queue is granted if possible *)
ProcessQueue ==
    /\ queue # <<>>
    /\ writers = {}
    LET front == Head(queue) IN
        IF front.type = "read" THEN
            /\ readers' = readers \cup {front.proc}
            /\ writers' = writers
            /\ queue'   = Tail(queue)
        ELSE
            /\ front.type = "write"
            /\ readers = {}
            /\ readers' = readers
            /\ writers' = {front.proc}
            /\ queue'   = Tail(queue)

(* An active reader or writer stops *)
Stop ==
    \E p \in Proc :
        /\ (p \in readers) \/ (p \in writers)
        /\ IF p \in readers
           THEN /\ readers' = readers \ {p}
                /\ writers' = writers
                /\ queue'   = queue
           ELSE /\ readers' = readers
                /\ writers' = {}
                /\ queue'   = queue

(* Next-state relation *)
Next ==
    \/ RequestRead
    \/ RequestWrite
    \/ ProcessQueue
    \/ Stop

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)

Spec ==
    Init
    /\ [][Next]_<<readers, writers, queue>>
    /\ WF_<<readers, writers, queue>>(RequestRead)
    /\ WF_<<readers, writers, queue>>(RequestWrite)
    /\ WF_<<readers, writers, queue>>(ProcessQueue)
    /\ WF_<<readers, writers, queue>>(Stop)

(* ----------------------------------------------------------------------
   Liveness property
   ---------------------------------------------------------------------- *)

Liveness ==
    \A p \in Proc :
        <> (p \in readers) /\ <> (p \in writers)

=============================================================================