---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

(* the model checker will substitute a concrete set for n *)
n == NumActors

VARIABLES readers, writers, queue

(* ------------------------------------------------------------------- *)
(* Type invariant *)
TypeOK ==
    /\ readers \subseteq n
    /\ writers \subseteq n
    /\ queue \in Seq([proc: n, op: {"Read","Write"}])
    /\ Cardinality(writers) <= 1
    /\ readers \cap writers = {}

(* ------------------------------------------------------------------- *)
(* Safety invariant *)
Safety ==
    readers \cap writers = {} /\ Cardinality(writers) <= 1

(* ------------------------------------------------------------------- *)
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = << >>

(* ------------------------------------------------------------------- *)
InQueue(p) == \E i \in DOMAIN queue : queue[i].proc = p

(* ------------------------------------------------------------------- *)
(* Request to read *)
RequestRead(p) ==
    /\ p \in n
    /\ ~ InQueue(p)
    /\ ~ (p \in readers) /\ ~ (p \in writers)
    /\ queue' = Append(queue, [proc |-> p, op |-> "Read"])
    /\ UNCHANGED << readers, writers >>

(* Request to write *)
RequestWrite(p) ==
    /\ p \in n
    /\ ~ InQueue(p)
    /\ ~ (p \in readers) /\ ~ (p \in writers)
    /\ queue' = Append(queue, [proc |-> p, op |-> "Write"])
    /\ UNCHANGED << readers, writers >>

(* ------------------------------------------------------------------- *)
(* Begin processing the front of the queue *)
Begin ==
    /\ queue # << >>
    /\ writers = {}
    /\ LET front == queue[1] IN
       \/ /\ front.op = "Read"
          /\ readers' = readers \cup {front.proc}
          /\ writers' = writers
          /\ queue'   = Tail(queue)
       \/ /\ front.op = "Write"
          /\ readers = {}
          /\ writers' = writers \cup {front.proc}
          /\ readers' = readers
          /\ queue'   = Tail(queue)

(* ------------------------------------------------------------------- *)
(* Stop activity *)
Stop(p) ==
    /\ p \in n
    /\ (p \in readers) \/ (p \in writers)
    /\ IF p \in readers THEN readers' = readers \ {p} ELSE readers' = readers
    /\ IF p \in writers THEN writers' = writers \ {p} ELSE writers' = writers
    /\ UNCHANGED queue

(* ------------------------------------------------------------------- *)
Next ==
    \/ \E p \in n : RequestRead(p)
    \/ \E p \in n : RequestWrite(p)
    \/ Begin
    \/ \E p \in n : Stop(p)

Spec ==
    Init /\ [][Next]_<<readers, writers, queue>>

(* ------------------------------------------------------------------- *)
(* Liveness: every process eventually reads and eventually writes *)
Liveness ==
    \A p \in n : <> (p \in readers) /\ <> (p \in writers)

====