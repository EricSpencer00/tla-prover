---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

(* operator required by the .cfg file *)
n == NumActors

VARIABLES Readers, Writers, Queue

(* helper: set of processes that have pending requests in the queue *)
QueueProcs(q) == { r.proc : r \in SeqToSet(q) }

(* initial state *)
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue = << >>

(* ------------------------------------------------------------------- *)
(* actions *)

RequestRead(p) ==
    /\ p \in NumActors
    /\ p \notin Readers
    /\ p \notin Writers
    /\ p \notin QueueProcs(Queue)
    /\ Queue' = Append(Queue, [type |-> "Read", proc |-> p])
    /\ UNCHANGED << Readers, Writers >>

RequestWrite(p) ==
    /\ p \in NumActors
    /\ p \notin Readers
    /\ p \notin Writers
    /\ p \notin QueueProcs(Queue)
    /\ Queue' = Append(Queue, [type |-> "Write", proc |-> p])
    /\ UNCHANGED << Readers, Writers >>

ProcessQueue ==
    /\ Len(Queue) > 0
    /\ Writers = {}
    /\ LET front == Head(Queue) IN
         IF front.type = "Read" THEN
            /\ Readers' = Readers \cup {front.proc}
            /\ Writers' = Writers
            /\ Queue'   = Tail(Queue)
         ELSE
            /\ front.type = "Write"
            /\ Readers = {}
            /\ Writers' = Writers \cup {front.proc}
            /\ Readers' = Readers
            /\ Queue'   = Tail(Queue)
    /\ UNCHANGED << >>

Stop(p) ==
    /\ p \in NumActors
    /\ (p \in Readers) \/ (p \in Writers)
    /\ IF p \in Readers THEN Readers' = Readers \ {p} ELSE Readers' = Readers
    /\ IF p \in Writers THEN Writers' = Writers \ {p} ELSE Writers' = Writers
    /\ UNCHANGED Queue

(* ------------------------------------------------------------------- *)
(* composite actions used for fairness *)

ReqRead == \E p \in NumActors : RequestRead(p)
ReqWrite == \E p \in NumActors : RequestWrite(p)
ProcQueue == ProcessQueue
StopAct == \E p \in NumActors : Stop(p)

Next ==
    \/ ReqRead
    \/ ReqWrite
    \/ ProcQueue
    \/ StopAct

vars == << Readers, Writers, Queue >>

(* ------------------------------------------------------------------- *)
(* specification, including weak fairness for all actions *)

Spec ==
    Init /\ [][Next]_vars
        /\ WF_vars(ReqRead)
        /\ WF_vars(ReqWrite)
        /\ WF_vars(ProcQueue)
        /\ WF_vars(StopAct)

(* ------------------------------------------------------------------- *)
(* invariants *)

TypeOK ==
    /\ Readers \subseteq NumActors
    /\ Writers \subseteq NumActors
    /\ Cardinality(Writers) <= 1
    /\ Queue \in Seq( [type : {"Read","Write"}, proc : NumActors] )

Safety ==
    /\ (Writers = {} \/ Readers = {})
    /\ Cardinality(Writers) <= 1

(* ------------------------------------------------------------------- *)
(* liveness property *)

Liveness ==
    \A p \in NumActors :
        /\ <> (p \in Readers)
        /\ <> (p \in Writers)
        /\ [] (p \in Readers => <> (p \notin Readers))
        /\ [] (p \in Writers => <> (p \notin Writers))

====