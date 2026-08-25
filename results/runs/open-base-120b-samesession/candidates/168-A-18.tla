---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

(* the set of actor identifiers *)
n == 1 .. NumActors

(* request record *)
Req == [proc : n, type : {"read", "write"}]

VARIABLES Readers, Writers, Queue

(*====================================================================*)
(* Types *)

TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Queue \in Seq(Req)
    /\ Cardinality(Writers) <= 1

(*====================================================================*)
(* Safety: no simultaneous readers and writers, at most one writer *)

Safety ==
    /\ Readers \cap Writers = {}
    /\ Cardinality(Writers) <= 1

(*====================================================================*)
(* Helper predicates *)

NotWaitingRead(p) ==
    ~(\E i \in DOMAIN Queue :
        Queue[i].proc = p /\ Queue[i].type = "read")

NotWaitingWrite(p) ==
    ~(\E i \in DOMAIN Queue :
        Queue[i].proc = p /\ Queue[i].type = "write")

(*====================================================================*)
(* Actions *)

RequestRead(p) ==
    /\ p \in n
    /\ NotWaitingRead(p)
    /\ Readers' = Readers
    /\ Writers' = Writers
    /\ Queue' = Append(Queue, [proc |-> p, type |-> "read"])

RequestWrite(p) ==
    /\ p \in n
    /\ NotWaitingWrite(p)
    /\ Readers' = Readers
    /\ Writers' = Writers
    /\ Queue' = Append(Queue, [proc |-> p, type |-> "write"])

ProcessQueue ==
    /\ Queue # <<>>
    /\ Writers = {}
    /\ LET front == Queue[1] IN
         IF front.type = "read" THEN
            /\ Readers' = Readers \cup {front.proc}
            /\ Writers' = Writers
            /\ Queue' = Tail(Queue)
         ELSE
            /\ Readers = {}
            /\ Writers' = {front.proc}
            /\ Queue' = Tail(Queue)

Stop(p) ==
    \/ /\ p \in Readers
       /\ Readers' = Readers \ {p}
       /\ Writers' = Writers
       /\ Queue' = Queue
    \/ /\ p \in Writers
       /\ Writers' = {}
       /\ Readers' = Readers
       /\ Queue' = Queue

(*====================================================================*)
(* Action groupings for fairness *)

ActionRequestRead == \E p \in n : RequestRead(p)
ActionRequestWrite == \E p \in n : RequestWrite(p)
ActionProcess == ProcessQueue
ActionStop == \E p \in n : Stop(p)

(*====================================================================*)
(* Next-state relation *)

Next ==
    ActionRequestRead
 \/ ActionRequestWrite
 \/ ActionProcess
 \/ ActionStop

(*====================================================================*)
(* Initialization *)

Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue = <<>>

(*====================================================================*)
(* Specification *)

Spec ==
    Init
    /\ [][Next]_<<Readers, Writers, Queue>>
    /\ WF_vars(ActionRequestRead)
    /\ WF_vars(ActionRequestWrite)
    /\ WF_vars(ActionProcess)
    /\ WF_vars(ActionStop)

(*====================================================================*)
(* Liveness property: every process eventually reads and eventually writes *)

Liveness ==
    \A p \in n :
        (<> (p \in Readers) /\ <> (p \in Writers))

====