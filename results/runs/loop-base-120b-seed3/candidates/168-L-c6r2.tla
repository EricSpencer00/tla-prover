---- MODULE ReadersWriters ----
EXTENDS FiniteSets, Sequences, Naturals

CONSTANT NumActors, n

VARIABLES Readers, Writers, Queue

(* record describing a request in the queue *)
Req == [ pid : n, type : {"read", "write"} ]

(* --------------------------------------------------------------------- *)
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = << >>

(* --------------------------------------------------------------------- *)
ReadReq(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ p \notin { q.pid : q \in Queue }
    /\ Queue' = Append(Queue, [pid |-> p, type |-> "read"])
    /\ UNCHANGED << Readers, Writers >>

WriteReq(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ p \notin { q.pid : q \in Queue }
    /\ Queue' = Append(Queue, [pid |-> p, type |-> "write"])
    /\ UNCHANGED << Readers, Writers >>

ProcessQueue ==
    /\ Queue # << >>
    /\ Writers = {}
    /\ LET front == Head(Queue) IN
         IF front.type = "read" THEN
            /\ Readers' = Readers \cup {front.pid}
            /\ Writers' = Writers
            /\ Queue'   = Tail(Queue)
         ELSE
            /\ front.type = "write"
            /\ Readers = {}
            /\ Writers' = {front.pid}
            /\ Queue'   = Tail(Queue)
    /\ UNCHANGED <<>>

StopAct(p) ==
    /\ p \in n
    /\ (p \in Readers \/ p \in Writers)
    /\ IF p \in Readers THEN
          Readers' = Readers \ {p}
       ELSE
          Readers' = Readers
    /\ IF p \in Writers THEN
          Writers' = Writers \ {p}
       ELSE
          Writers' = Writers
    /\ UNCHANGED Queue

(* --------------------------------------------------------------------- *)
ReadReqAction  == \E p \in n : ReadReq(p)
WriteReqAction == \E p \in n : WriteReq(p)
StopAction     == \E p \in n : StopAct(p)
ProcessAction  == ProcessQueue

Next ==
    \/ ReadReqAction
    \/ WriteReqAction
    \/ ProcessAction
    \/ StopAction

(* --------------------------------------------------------------------- *)
Spec ==
    Init /\
    [][Next]_<<Readers, Writers, Queue>> /\
    WF_<<Readers, Writers, Queue>>(ReadReqAction) /\
    WF_<<Readers, Writers, Queue>>(WriteReqAction) /\
    WF_<<Readers, Writers, Queue>>(ProcessAction) /\
    WF_<<Readers, Writers, Queue>>(StopAction)

(* --------------------------------------------------------------------- *)
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Cardinality(Writers) <= 1
    /\ Queue \in Seq(Req)

Safety ==
    /\ (Writers = {} \/ Readers = {})
    /\ Cardinality(Writers) <= 1

Liveness ==
    \A p \in n :
        <> (p \in Readers) /\ <> (p \in Writers)

====