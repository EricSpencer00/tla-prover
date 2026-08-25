---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

(* The set of process identifiers (can be overridden by the .cfg) *)
n == 1..NumActors

VARIABLES Readers, Writers, Queue

(* ---------------------------------------------------------------------- *)
(* Helper definitions *)

(* Set of processes that currently have a pending request in the queue *)
QueueProcs == { Queue[i].proc : i \in 1..Len(Queue) }

(* ---------------------------------------------------------------------- *)
(* Initial state *)

Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = <<>>

(* ---------------------------------------------------------------------- *)
(* Actions *)

RequestRead(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ p \notin QueueProcs
    /\ Queue' = Append(Queue, [proc |-> p, type |-> "Read"])
    /\ UNCHANGED <<Readers, Writers>>

RequestWrite(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ p \notin QueueProcs
    /\ Queue' = Append(Queue, [proc |-> p, type |-> "Write"])
    /\ UNCHANGED <<Readers, Writers>>

ProcessQueue ==
    /\ Queue # <<>>
    /\ Writers = {}
    /\ LET front == Queue[1] IN
       \/ /\ front.type = "Read"
          /\ Readers' = Readers \cup {front.proc}
          /\ Writers' = Writers
          /\ Queue'   = Tail(Queue)
       \/ /\ front.type = "Write"
          /\ Readers = {}
          /\ Readers' = {}
          /\ Writers' = Writers \cup {front.proc}
          /\ Queue'   = Tail(Queue)

Stop(p) ==
    /\ p \in Readers \/ p \in Writers
    /\ IF p \in Readers
          THEN Readers' = Readers \ {p} /\ Writers' = Writers
          ELSE Readers' = Readers /\ Writers' = Writers \ {p}
    /\ UNCHANGED Queue

(* ---------------------------------------------------------------------- *)
(* Next-state relation *)

Next ==
    \/ \E p \in n : RequestRead(p)
    \/ \E p \in n : RequestWrite(p)
    \/ ProcessQueue
    \/ \E p \in n : Stop(p)

vars == <<Readers, Writers, Queue>>

(* ---------------------------------------------------------------------- *)
(* Specification *)

Spec ==
    Init /\ [][Next]_vars
    /\ \A p \in n :
          WF_vars(RequestRead(p))
          /\ WF_vars(RequestWrite(p))
          /\ WF_vars(Stop(p))
    /\ WF_vars(ProcessQueue)

(* ---------------------------------------------------------------------- *)
(* Invariants *)

TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Readers \cap Writers = {}
    /\ (Queue = <<>> \/
        ( /\ Len(Queue) >= 1
          /\ \A i \in 1..Len(Queue) :
                Queue[i].proc \in n
                /\ (Queue[i].type = "Read" \/ Queue[i].type = "Write")
        ))
    /\ \A i, j \in 1..Len(Queue) : i # j => Queue[i].proc # Queue[j].proc

Safety ==
    /\ (Writers = {} \/ Readers = {})
    /\ Cardinality(Writers) <= 1

(* ---------------------------------------------------------------------- *)
(* Liveness property *)

Liveness ==
    \A p \in n :
        (<> (p \in Readers))      /\  (* eventually reads *)
        (<> (p \in Writers))      /\  (* eventually writes *)
        ([] (p \in Readers => <> (p \notin Readers))) /\  (* stops reading *)
        ([] (p \in Writers => <> (p \notin Writers)))    (* stops writing *)

====