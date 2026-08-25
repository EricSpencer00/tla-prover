---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT NumActors

(* the set of actor identifiers *)
n == 1..NumActors

VARIABLES Readers, Writers, Queue

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)

ReaderSet == Readers
WriterSet == Writers
Request == Queue

IsRead(req) == req.mode = "read"
IsWrite(req) == req.mode = "write"

InQueue(p, m) == \E q \in Queue : q.pid = p /\ q.mode = m

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)

Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = << >>

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

RequestRead(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ ~InQueue(p, "read")
    /\ Queue' = Append(Queue, [pid |-> p, mode |-> "read"])
    /\ UNCHANGED << Readers, Writers >>

RequestWrite(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ ~InQueue(p, "write")
    /\ Queue' = Append(Queue, [pid |-> p, mode |-> "write"])
    /\ UNCHANGED << Readers, Writers >>

ProcessQueue ==
    /\ Queue # << >>
    /\ LET front == Head(Queue) IN
          IF IsRead(front) THEN
              /\ Writers = {}
              /\ Readers' = Readers \cup {front.pid}
              /\ Writers' = Writers
              /\ Queue'   = Tail(Queue)
          ELSE
              /\ Writers = {}
              /\ Readers = {}
              /\ Writers' = Writers \cup {front.pid}
              /\ Readers' = Readers
              /\ Queue'   = Tail(Queue)

StopRead(p) ==
    /\ p \in Readers
    /\ Readers' = Readers \ {p}
    /\ UNCHANGED << Writers, Queue >>

StopWrite(p) ==
    /\ p \in Writers
    /\ Writers' = Writers \ {p}
    /\ UNCHANGED << Readers, Queue >>

(* ----------------------------------------------------------------------
   Composite actions for the Next relation
   ---------------------------------------------------------------------- *)

RequestReadAction == \E p \in n : RequestRead(p)
RequestWriteAction == \E p \in n : RequestWrite(p)
StopReadAction    == \E p \in Readers : StopRead(p)
StopWriteAction   == \E p \in Writers : StopWrite(p)
ProcessQueueAction == ProcessQueue

Next ==
    \/ RequestReadAction
    \/ RequestWriteAction
    \/ ProcessQueueAction
    \/ StopReadAction
    \/ StopWriteAction

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)

Spec ==
    Init /\ [][Next]_<<Readers, Writers, Queue>>
    /\ WF_<<Readers, Writers, Queue>>(RequestReadAction)
    /\ WF_<<Readers, Writers, Queue>>(RequestWriteAction)
    /\ WF_<<Readers, Writers, Queue>>(ProcessQueueAction)
    /\ WF_<<Readers, Writers, Queue>>(StopReadAction)
    /\ WF_<<Readers, Writers, Queue>>(StopWriteAction)

(* ----------------------------------------------------------------------
   Type correctness invariant
   ---------------------------------------------------------------------- *)

TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Readers \cap Writers = {}
    /\ Queue \in Seq([pid : n, mode : {"read","write"}])

(* ----------------------------------------------------------------------
   Safety invariant (mutual exclusion)
   ---------------------------------------------------------------------- *)

Safety ==
    /\ Readers \cap Writers = {}
    /\ Cardinality(Writers) <= 1

(* ----------------------------------------------------------------------
   Liveness properties
   ---------------------------------------------------------------------- *)

Liveness ==
    /\ \A p \in n : <> (p \in Readers)            \* every process eventually reads
    /\ \A p \in n : <> (p \in Writers)            \* every process eventually writes
    /\ \A p \in n : [] (p \in Readers => <> (p \notin Readers))  \* readers eventually stop
    /\ \A p \in n : [] (p \in Writers => <> (p \notin Writers))  \* writers eventually stop

=============================================================================