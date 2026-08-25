---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

(* the .cfg file will replace NumActors with a concrete value;
   we provide a convenient alias *)
n == NumActors

(* the set of all actor processes *)
Actor == 1 .. NumActors

(* a request record *)
Req == [proc : Actor, type : {"Read", "Write"}]

VARIABLES Readers, Writers, Queue

(* ---------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue = << >>

(* ---------------------------------------------------------------------- *)
(* Helper definitions *)

Head(q) == q[1]
Tail(q) == SubSeq(q, 2, Len(q))

(* ---------------------------------------------------------------------- *)
(* Actions *)

RequestRead(p) ==
    /\ p \in Actor
    /\ p \notin Readers
    /\ p \notin Writers
    /\ \A r \in Queue : r.proc # p
    /\ Readers' = Readers
    /\ Writers' = Writers
    /\ Queue' = Append(Queue, [proc |-> p, type |-> "Read"])

RequestWrite(p) ==
    /\ p \in Actor
    /\ p \notin Readers
    /\ p \notin Writers
    /\ \A r \in Queue : r.proc # p
    /\ Readers' = Readers
    /\ Writers' = Writers
    /\ Queue' = Append(Queue, [proc |-> p, type |-> "Write"])

BeginProcessing ==
    /\ Len(Queue) > 0
    /\ Writers = {}
    /\ LET r == Head(Queue) IN
       IF r.type = "Read" THEN
          /\ Readers' = Readers \cup {r.proc}
          /\ Writers' = Writers
          /\ Queue' = Tail(Queue)
       ELSE
          /\ Readers = {}
          /\ Writers' = Writers \cup {r.proc}
          /\ Queue' = Tail(Queue)
    /\ UNCHANGED << Readers, Writers, Queue >> \ {Readers', Writers', Queue'}

StopRead(p) ==
    /\ p \in Readers
    /\ Readers' = Readers \ {p}
    /\ Writers' = Writers
    /\ Queue' = Queue

StopWrite(p) ==
    /\ p \in Writers
    /\ Writers' = Writers \ {p}
    /\ Readers' = Readers
    /\ Queue' = Queue

(* ---------------------------------------------------------------------- *)
(* Next-state relation *)
Next ==
    \/ \E p \in Actor : RequestRead(p)
    \/ \E p \in Actor : RequestWrite(p)
    \/ BeginProcessing
    \/ \E p \in Actor : StopRead(p)
    \/ \E p \in Actor : StopWrite(p)

(* ---------------------------------------------------------------------- *)
(* Specification *)
Spec ==
    Init /\ [][Next]_<<Readers, Writers, Queue>> /\ WF_vars(Next)

(* ---------------------------------------------------------------------- *)
(* Type correctness invariant *)
TypeOK ==
    /\ Readers \subseteq Actor
    /\ Writers \subseteq Actor
    /\ Queue \in Seq(Req)

(* ---------------------------------------------------------------------- *)
(* Safety invariant *)
Safety ==
    /\ (Writers = {} => Readers = {})
    /\ Cardinality(Writers) <= 1

(* ---------------------------------------------------------------------- *)
(* Liveness property *)
Liveness ==
    \A p \in Actor :
        /\ <> (p \in Readers)               \* every process eventually reads
        /\ <> (p \in Writers)               \* every process eventually writes
        /\ []<>(p \in Readers => <> (p \notin Readers))   \* readers eventually stop
        /\ []<>(p \in Writers => <> (p \notin Writers))   \* writers eventually stop

====