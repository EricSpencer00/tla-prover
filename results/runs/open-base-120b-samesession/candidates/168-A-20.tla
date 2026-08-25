---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

(* the set of actor identifiers; may be overridden by the .cfg file *)
n == {1, 2, 3, 4}

Proc == 1..NumActors

VARIABLES Readers, Writers, Queue

vars == << Readers, Writers, Queue >>

(* ------------------------------------------------------------------- *)
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = << >>

(* ------------------------------------------------------------------- *)
(* A process requests read access and is not already waiting to read. *)
RequestRead(p) ==
    /\ p \in Proc
    /\ ~(\E i \in 1..Len(Queue) :
            Queue[i].proc = p /\ Queue[i].type = "read")
    /\ Queue' = Append(Queue, [type |-> "read", proc |-> p])
    /\ UNCHANGED << Readers, Writers >>

(* A process requests write access and is not already waiting to write. *)
RequestWrite(p) ==
    /\ p \in Proc
    /\ ~(\E i \in 1..Len(Queue) :
            Queue[i].proc = p /\ Queue[i].type = "write")
    /\ Queue' = Append(Queue, [type |-> "write", proc |-> p])
    /\ UNCHANGED << Readers, Writers >>

(* ------------------------------------------------------------------- *)
(* The head of the queue is granted access if it is safe to do so. *)
ProcessQueue ==
    /\ Len(Queue) > 0
    /\ Writers = {}
    /\ LET r == Queue[1] IN
        IF r.type = "read" THEN
            /\ Readers' = Readers \cup {r.proc}
            /\ Writers' = Writers
            /\ Queue'   = Tail(Queue)
        ELSE
            /\ Readers = {}               \* no readers before a writer may start
            /\ Writers' = {r.proc}
            /\ Readers' = Readers
            /\ Queue'   = Tail(Queue)

(* ------------------------------------------------------------------- *)
(* A process that is currently active may stop. *)
Stop(p) ==
    /\ p \in Proc
    /\ (p \in Readers \/ p \in Writers)
    /\ IF p \in Readers THEN
            /\ Readers' = Readers \ {p}
            /\ Writers' = Writers
       ELSE
            /\ Writers' = {}
            /\ Readers' = Readers
    /\ Queue' = Queue

(* ------------------------------------------------------------------- *)
RequestReadAct  == \E p \in Proc : RequestRead(p)
RequestWriteAct == \E p \in Proc : RequestWrite(p)
ProcessQueueAct == ProcessQueue
StopAct         == \E p \in Proc : Stop(p)

Next == RequestReadAct \/ RequestWriteAct \/ ProcessQueueAct \/ StopAct

(* ------------------------------------------------------------------- *)
Spec ==
    Init /\ [][Next]_vars
        /\ WF_vars(RequestReadAct)
        /\ WF_vars(RequestWriteAct)
        /\ WF_vars(ProcessQueueAct)
        /\ WF_vars(StopAct)

(* ------------------------------------------------------------------- *)
TypeOK ==
    /\ Readers \subseteq Proc
    /\ Writers \subseteq Proc
    /\ Cardinality(Writers) <= 1
    /\ Queue \in Seq([type : {"read","write"}, proc : Proc])

Safety ==
    /\ (Writers # {} => Readers = {})
    /\ Cardinality(Writers) <= 1

Liveness ==
    \A p \in Proc : <> (p \in Readers) /\ <> (p \in Writers)

====