---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

(*--------------------------------------------------------------------
  Set of all actor processes.
--------------------------------------------------------------------*)
n == 1 .. NumActors
Actor == n

(*--------------------------------------------------------------------
  Definition of a request in the waiting queue.
--------------------------------------------------------------------*)
Req == [proc : Actor, type : {"read", "write"}]

VARIABLES Readers, Writers, Queue

(*--------------------------------------------------------------------
  Type invariant.
--------------------------------------------------------------------*)
TypeOK ==
    /\ Readers \subseteq Actor
    /\ Writers \subseteq Actor
    /\ Readers \cap Writers = {}          \* Readers and Writers are disjoint
    /\ Queue \in Seq(Req)

(*--------------------------------------------------------------------
  Initial state.
--------------------------------------------------------------------*)
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = << >>

(*--------------------------------------------------------------------
  Action: a process requests to read.
--------------------------------------------------------------------*)
RequestRead(p) ==
    /\ p \in Actor
    /\ p \notin Readers
    /\ p \notin Writers
    /\ \A i \in 1 .. Len(Queue) : Queue[i].proc # p
    /\ Queue' = Append(Queue, [proc |-> p, type |-> "read"])
    /\ UNCHANGED <<Readers, Writers>>

(*--------------------------------------------------------------------
  Action: a process requests to write.
--------------------------------------------------------------------*)
RequestWrite(p) ==
    /\ p \in Actor
    /\ p \notin Readers
    /\ p \notin Writers
    /\ \A i \in 1 .. Len(Queue) : Queue[i].proc # p
    /\ Queue' = Append(Queue, [proc |-> p, type |-> "write"])
    /\ UNCHANGED <<Readers, Writers>>

(*--------------------------------------------------------------------
  Action: process the request at the front of the queue.
--------------------------------------------------------------------*)
ProcessQueue ==
    /\ Len(Queue) > 0
    /\ Writers = {}                           \* no writer active
    /\ LET front == Queue[1] IN
       IF front.type = "read" THEN
          /\ Readers' = Readers \cup {front.proc}
          /\ Writers' = Writers
          /\ Queue'   = Tail(Queue)
       ELSE \* front.type = "write"
          /\ Readers = {}                     \* no readers active
          /\ Writers' = Writers \cup {front.proc}
          /\ Readers' = Readers
          /\ Queue'   = Tail(Queue)
    /\ UNCHANGED <<>>

(*--------------------------------------------------------------------
  Action: a process stops its current activity.
--------------------------------------------------------------------*)
Stop(p) ==
    /\ p \in Actor
    /\ (p \in Readers \/ p \in Writers)
    /\ IF p \in Readers THEN
          /\ Readers' = Readers \ {p}
          /\ Writers' = Writers
       ELSE
          /\ Writers' = Writers \ {p}
          /\ Readers' = Readers
    /\ UNCHANGED Queue

(*--------------------------------------------------------------------
  Composite next-state relation.
--------------------------------------------------------------------*)
Next ==
    \/ \E p \in Actor : RequestRead(p)
    \/ \E p \in Actor : RequestWrite(p)
    \/ ProcessQueue
    \/ \E p \in Actor : Stop(p)

(*--------------------------------------------------------------------
  Fairness assumptions (weak fairness for all actions).
--------------------------------------------------------------------*)
RequestReadFair ==
    \E p \in Actor : RequestRead(p)

RequestWriteFair ==
    \E p \in Actor : RequestWrite(p)

StopFair ==
    \E p \in Actor : Stop(p)

ProcessQueueFair == ProcessQueue

(*--------------------------------------------------------------------
  Specification.
--------------------------------------------------------------------*)
Spec ==
    Init /\ [][Next]_<<Readers, Writers, Queue>>
    /\ WF_<<Readers, Writers, Queue>>(RequestReadFair)
    /\ WF_<<Readers, Writers, Queue>>(RequestWriteFair)
    /\ WF_<<Readers, Writers, Queue>>(ProcessQueueFair)
    /\ WF_<<Readers, Writers, Queue>>(StopFair)

(*--------------------------------------------------------------------
  Safety property: no readers and writers simultaneously,
  and at most one writer.
--------------------------------------------------------------------*)
Safety ==
    /\ Readers = {} \/ Writers = {}
    /\ Cardinality(Writers) <= 1

(*--------------------------------------------------------------------
  Liveness property: every process eventually reads and writes,
  and active readers/writers eventually stop.
--------------------------------------------------------------------*)
Liveness ==
    \A p \in Actor :
        /\ <> (p \in Readers)                \* eventually reads
        /\ <> (p \in Writers)                \* eventually writes
        /\ [] (p \in Readers => <> (p \notin Readers))   \* readers stop
        /\ [] (p \in Writers => <> (p \notin Writers))   \* writers stop

====