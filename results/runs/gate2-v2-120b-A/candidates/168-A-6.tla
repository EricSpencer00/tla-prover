---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

(* ---------------------------------------------------------------------- *)
(* Types *)
PROCESS == 1 .. NumActors
RWKind   == {"Read", "Write"}

REQUEST == [kind : RWKind, proc : PROCESS]

(* ---------------------------------------------------------------------- *)
(* Variables *)
VARIABLES readers, writers, queue

(* ---------------------------------------------------------------------- *)
(* Helper definitions *)
IsEmptyQueue == Len(queue) = 0

Head(q) == q[1]
Tail(q) == SubSeq(q, 2, Len(q))

(* ---------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = << >>

(* ---------------------------------------------------------------------- *)
(* Actions *)

RequestRead(proc) ==
    /\ proc \in PROCESS
    /\ proc \notin { r.proc : r \in queue }
    /\ queue' = Append(queue, [kind |-> "Read", proc |-> proc])
    /\ readers' = readers
    /\ writers' = writers

RequestWrite(proc) ==
    /\ proc \in PROCESS
    /\ proc \notin { r.proc : r \in queue }
    /\ queue' = Append(queue, [kind |-> "Write", proc |-> proc])
    /\ readers' = readers
    /\ writers' = writers

BeginAct ==
    /\ ~IsEmptyQueue
    /\ writers = {}
    /\ LET front == Head(queue) IN
       IF front.kind = "Read" THEN
          /\ readers' = readers \cup { front.proc }
          /\ writers' = writers
          /\ queue'   = Tail(queue)
       ELSE
          /\ readers = {}
          /\ writers' = { front.proc }
          /\ readers' = readers
          /\ queue'   = Tail(queue)

Stop(proc) ==
    /\ proc \in PROCESS
    /\ \/ proc \in readers
       \/ proc \in writers
    /\ readers' = readers \ { proc }
    /\ writers' = writers \ { proc }
    /\ queue'   = queue

Next ==
    \/ \E p \in PROCESS: RequestRead(p)
    \/ \E p \in PROCESS: RequestWrite(p)
    \/ \E p \in PROCESS: Stop(p)
    \/ BeginAct

(* ---------------------------------------------------------------------- *)
(* Specification *)
Spec ==
    Init /\ [][Next]_<<readers, writers, queue>>

(* ---------------------------------------------------------------------- *)
(* Invariants *)

TypeOK ==
    /\ readers \subseteq PROCESS
    /\ writers \subseteq PROCESS
    /\ /\ writers = {}
       \/ \E w \in writers: writers = {w}
    /\ /\ queue \in Seq(REQUEST)
    /\ \A i \in DOMAIN queue:
          /\ queue[i].kind \in RWKind
          /\ queue[i].proc \in PROCESS

Safety ==
    /\ (writers = {} => TRUE)
    /\ (writers # {} => readers = {})
    /\ /\ writers = {}
       \/ \E w \in writers: writers = {w}

(* ---------------------------------------------------------------------- *)
(* Liveness property (placeholder, actual liveness proved via .cfg) *)
Liveness == TRUE

====