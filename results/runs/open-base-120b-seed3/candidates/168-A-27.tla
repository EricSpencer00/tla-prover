---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

(* Set of actor identifiers *)
n == 1..NumActors

VARIABLES Readers, Writers, Queue

(* --------------------------------------------------------------------- *)
(* Type invariant *)
TypeOK ==
  /\ Readers \subseteq n
  /\ Writers \subseteq n
  /\ Cardinality(Writers) <= 1
  /\ Queue \in Seq([proc : n, typ : {"read","write"}])

(* Safety: never both readers and a writer, and at most one writer *)
Safety ==
  /\ (Writers = {} \/ Readers = {})
  /\ Cardinality(Writers) <= 1

(* --------------------------------------------------------------------- *)
(* Initial state *)
Init ==
  /\ Readers = {}
  /\ Writers = {}
  /\ Queue   = <<>>

(* Helper: does process p already have a pending request? *)
Waiting(p) == \E q \in Queue: q.proc = p

(* --------------------------------------------------------------------- *)
(* Actions *)

(* Request to read *)
ReqRead(p) ==
  /\ p \in n
  /\ p \notin Readers
  /\ p \notin Writers
  /\ ~Waiting(p)
  /\ Queue' = Queue \o <<[proc |-> p, typ |-> "read"]>>
  /\ Readers' = Readers
  /\ Writers' = Writers

(* Request to write *)
ReqWrite(p) ==
  /\ p \in n
  /\ p \notin Readers
  /\ p \notin Writers
  /\ ~Waiting(p)
  /\ Queue' = Queue \o <<[proc |-> p, typ |-> "write"]>>
  /\ Readers' = Readers
  /\ Writers' = Writers

(* Process the head of the queue *)
ProcessQueue ==
  /\ Queue # <<>>
  /\ LET first == Queue[1] IN
        /\ (first.typ = "read") \/ (first.typ = "write" /\ Readers = {})
  /\ Writers = {}          \* no writer currently active
  /\ IF first.typ = "read" THEN
        /\ Readers' = Readers \cup {first.proc}
        /\ Writers' = Writers
        /\ Queue'   = Tail(Queue)
     ELSE
        /\ Readers' = Readers
        /\ Writers' = {first.proc}
        /\ Queue'   = Tail(Queue)

(* Stop activity (reading or writing) *)
Stop(p) ==
  /\ p \in n
  /\ (p \in Readers \/ p \in Writers)
  /\ Readers' = Readers \ {p}
  /\ Writers' = IF p \in Writers THEN {} ELSE Writers
  /\ Queue'   = Queue

(* --------------------------------------------------------------------- *)
(* Action aggregations *)

ReqReadAction  == \E p \in n: ReqRead(p)
ReqWriteAction == \E p \in n: ReqWrite(p)
ProcessAction  == ProcessQueue
StopAction     == \E p \in n: Stop(p)

Next ==
  \/ ReqReadAction
  \/ ReqWriteAction
  \/ ProcessAction
  \/ StopAction

(* --------------------------------------------------------------------- *)
(* Specification with weak fairness on all actions *)

Spec ==
  Init
  /\ [][Next]_<<Readers, Writers, Queue>>
  /\ WF_<<Readers, Writers, Queue>>(ReqReadAction)
  /\ WF_<<Readers, Writers, Queue>>(ReqWriteAction)
  /\ WF_<<Readers, Writers, Queue>>(ProcessAction)
  /\ WF_<<Readers, Writers, Queue>>(StopAction)

(* --------------------------------------------------------------------- *)
(* Liveness property *)

Liveness ==
  /\ \A p \in n: <> (p \in Readers)               \* every process eventually reads
  /\ \A p \in n: <> (p \in Writers)               \* every process eventually writes
  /\ \A p \in n: [] (p \in Readers => <> (p \notin Readers))  \* readers eventually stop
  /\ \A p \in n: [] (p \in Writers => <> (p \notin Writers))  \* writers eventually stop

=============================================================================