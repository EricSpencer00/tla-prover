---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

(* Set of actor identifiers *)
n == 1..NumActors

VARIABLES readers, writers, queue

(* Record type for a request *)
Req == [pid : n, kind : {"Read","Write"}]

(* Type invariant *)
TypeOK == /\ readers \in SUBSET n
          /\ writers \in SUBSET n
          /\ queue \in Seq(Req)

(* Initial state *)
Init == /\ readers = {}
        /\ writers = {}
        /\ queue = <<>>

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

(* A process requests a read *)
RequestRead(p) ==
    /\ p \in n
    /\ ~(\E i \in 1..Len(queue) : queue[i].pid = p /\ queue[i].kind = "Read")
    /\ queue' = queue \o <<[pid |-> p, kind |-> "Read"]>>
    /\ UNCHANGED <<readers, writers>>

(* A process requests a write *)
RequestWrite(p) ==
    /\ p \in n
    /\ ~(\E i \in 1..Len(queue) : queue[i].pid = p /\ queue[i].kind = "Write")
    /\ queue' = queue \o <<[pid |-> p, kind |-> "Write"]>>
    /\ UNCHANGED <<readers, writers>>

ReqRead  == \E p \in n : RequestRead(p)
ReqWrite == \E p \in n : RequestWrite(p)

(* Process the request at the front of the queue *)
Process ==
    /\ Len(queue) > 0
    /\ LET front == queue[1] IN
          /\ writers = {}
          /\ (front.kind = "Write" => readers = {})
          /\ IF front.kind = "Read"
                THEN readers' = readers \cup {front.pid}
                     /\ writers' = writers
                ELSE readers' = {}
                     /\ writers' = {front.pid}
          /\ queue' = Tail(queue)
    /\ UNCHANGED <<>>

(* A process stops its current activity *)
StopAct ==
    \E p \in n :
        ( /\ p \in readers
           /\ readers' = readers \ {p}
           /\ UNCHANGED <<writers, queue>> )
     \/ ( /\ p \in writers
           /\ writers' = {}
           /\ UNCHANGED <<readers, queue>> )

(* Next-state relation *)
Next == ReqRead \/ ReqWrite \/ Process \/ StopAct

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)

Spec ==
    Init
    /\ [][Next]_<<readers, writers, queue>>
    /\ WF_<<readers, writers, queue>>(ReqRead)
    /\ WF_<<readers, writers, queue>>(ReqWrite)
    /\ WF_<<readers, writers, queue>>(Process)
    /\ WF_<<readers, writers, queue>>(StopAct)

(* ----------------------------------------------------------------------
   Properties
   ---------------------------------------------------------------------- *)

(* Safety: no simultaneous readers and writers, at most one writer *)
Safety ==
    /\ (writers = {} \/ readers = {})
    /\ Cardinality(writers) <= 1

(* Liveness: every process eventually reads and eventually writes *)
Liveness == \A p \in n : <> (p \in readers) /\ <> (p \in writers)

====