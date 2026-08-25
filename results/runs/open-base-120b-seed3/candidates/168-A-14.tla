---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

(* the set of all actor identifiers *)
n == 1..NumActors

VARIABLES Readers, Writers, Queue

(* ---------------------------------------------------------------------- *)
(*   Types                                                               *)
(* ---------------------------------------------------------------------- *)

Req == [proc : n, kind : {"read", "write"}]

TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Queue \in Seq(Req)

(* ---------------------------------------------------------------------- *)
(*   Initial state                                                       *)
(* ---------------------------------------------------------------------- *)

Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = << >>

(* ---------------------------------------------------------------------- *)
(*   Actions                                                             *)
(* ---------------------------------------------------------------------- *)

RequestRead(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ ~(\E q \in Queue: q.proc = p)          \* not already waiting
    /\ Readers' = Readers
    /\ Writers' = Writers
    /\ Queue'   = Append(Queue, [proc |-> p, kind |-> "read"])

RequestWrite(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ ~(\E q \in Queue: q.proc = p)          \* not already waiting
    /\ Readers' = Readers
    /\ Writers' = Writers
    /\ Queue'   = Append(Queue, [proc |-> p, kind |-> "write"])

ProcessQueue ==
    /\ Queue # << >>                         \* queue not empty
    /\ Writers = {}                          \* no writer currently active
    /\ LET req == Head(Queue) IN
       /\ CASE req.kind = "read" ->
              /\ Readers' = Readers \cup {req.proc}
              /\ Writers' = Writers
          [] req.kind = "write" ->
              /\ Readers = {}                \* no readers while a writer may start
              /\ Readers' = Readers
              /\ Writers' = Writers \cup {req.proc}
        /\ Queue' = Tail(Queue)

Stop(p) ==
    /\ p \in Readers \/ p \in Writers
    /\ IF p \in Readers THEN Readers' = Readers \ {p} ELSE Readers' = Readers
    /\ IF p \in Writers THEN Writers' = Writers \ {p} ELSE Writers' = Writers
    /\ Queue' = Queue

(* ---------------------------------------------------------------------- *)
(*   Next relation                                                       *)
(* ---------------------------------------------------------------------- *)

Next ==
    \/ \E p \in n: RequestRead(p)
    \/ \E p \in n: RequestWrite(p)
    \/ ProcessQueue
    \/ \E p \in n: Stop(p)

(* ---------------------------------------------------------------------- *)
(*   Specification                                                       *)
(* ---------------------------------------------------------------------- *)

ReadReq  == \E p \in n: RequestRead(p)
WriteReq == \E p \in n: RequestWrite(p)
ProcAct  == ProcessQueue
StopAct  == \E p \in n: Stop(p)

Spec ==
    Init /\ [][Next]_<<Readers, Writers, Queue>> /\
    WF_vars(ReadReq) /\ WF_vars(WriteReq) /\ WF_vars(ProcAct) /\ WF_vars(StopAct)

(* ---------------------------------------------------------------------- *)
(*   Safety property                                                     *)
(* ---------------------------------------------------------------------- *)

Safety ==
    /\ Readers \cap Writers = {}
    /\ Cardinality(Writers) <= 1

(* ---------------------------------------------------------------------- *)
(*   Liveness property                                                   *)
(* ---------------------------------------------------------------------- *)

Liveness ==
    \A p \in n :
        /\ [] (p \in Readers => <> (p \notin Readers))
        /\ [] (p \in Writers => <> (p \notin Writers))
        /\ <> (p \in Readers)
        /\ <> (p \in Writers)

====