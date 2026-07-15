---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

(* -------------------------------------------------------------------------- *)
(* Types and sets                                                             *)
(* -------------------------------------------------------------------------- *)

Proc == 1..NumActors

RequestType == {"Read", "Write"}

Request == [type : RequestType, proc : Proc]

(* -------------------------------------------------------------------------- *)
(* Variables                                                                  *)
(* -------------------------------------------------------------------------- *)

VARIABLES readers, writers, queue

(* -------------------------------------------------------------------------- *)
(* Helper definitions                                                         *)
(* -------------------------------------------------------------------------- *)

Readers == readers
Writers == writers
Queue   == queue

(* -------------------------------------------------------------------------- *)
(* Initial state                                                              *)
(* -------------------------------------------------------------------------- *)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = <<>>

(* -------------------------------------------------------------------------- *)
(* Actions                                                                    *)
(* -------------------------------------------------------------------------- *)

(* Process i requests to read *)
RequestRead(i) ==
    /\ i \in Proc
    /\ ~(\E q \in queue : q.type = "Read" /\ q.proc = i)  \* not already waiting to read
    /\ queue' = Append(queue, [type |-> "Read", proc |-> i])
    /\ UNCHANGED <<readers, writers>>

(* Process i requests to write *)
RequestWrite(i) ==
    /\ i \in Proc
    /\ ~(\E q \in queue : q.type = "Write" /\ q.proc = i) \* not already waiting to write
    /\ queue' = Append(queue, [type |-> "Write", proc |-> i])
    /\ UNCHANGED <<readers, writers>>

(* Process the head of the queue, granting access if possible *)
Begin =
    /\ Len(queue) > 0
    /\ LET head == Head(queue) IN
       IF head.type = "Read" THEN
          /\ writers = {}               \* no writer active
          /\ readers' = readers \cup {head.proc}
          /\ writers' = writers
          /\ queue'   = Tail(queue)
       ELSE  \* head.type = "Write"
          /\ readers = {}               \* no readers active
          /\ writers' = writers \cup {head.proc}
          /\ readers' = readers
          /\ queue'   = Tail(queue)

(* Any active reader may stop *)
StopRead(i) ==
    /\ i \in readers
    /\ readers' = readers \ {i}
    /\ UNCHANGED <<writers, queue>>

(* Any active writer may stop *)
StopWrite(i) ==
    /\ i \in writers
    /\ writers' = writers \ {i}
    /\ UNCHANGED <<readers, queue>>

(* -------------------------------------------------------------------------- *)
(* Next-state relation                                                        *)
(* -------------------------------------------------------------------------- *)

Next ==
    \/ \E i \in Proc : RequestRead(i)
    \/ \E i \in Proc : RequestWrite(i)
    \/ Begin
    \/ \E i \in Proc : StopRead(i)
    \/ \E i \in Proc : StopWrite(i)

(* -------------------------------------------------------------------------- *)
(* Specification                                                              *)
(* -------------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<readers, writers, queue>>

(* -------------------------------------------------------------------------- *)
(* Type invariant (helps TLC)                                                 *)
(* -------------------------------------------------------------------------- *)

TypeOK ==
    /\ readers \subseteq Proc
    /\ writers \subseteq Proc
    /\ writers \subseteq Proc
    /\ queue \in Seq(Request)

(* -------------------------------------------------------------------------- *)
(* Safety invariant: no simultaneous readers and writers, and at most one writer *)
(* -------------------------------------------------------------------------- *)

Safety ==
    /\ ~(writers # {} /\ readers # {})
    /\ Cardinality(writers) <= 1

(* -------------------------------------------------------------------------- *)
(* Liveness property: each process eventually performs a read and a write      *)
(* -------------------------------------------------------------------------- *)

Liveness ==
    /\ \A i \in Proc : <> (i \in readers)   \* eventually reads
    /\ \A i \in Proc : <> (i \in writers)   \* eventually writes

====