---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

(*--------------------------------------------------------------------
  Definition of the finite set of actors.
  The configuration file substitutes the identifier `n` for `NumActors`.
--------------------------------------------------------------------*)
n == 1..NumActors

VARIABLES Readers, Writers, Queue

(*--------------------------------------------------------------------
  Types of requests in the waiting queue.
--------------------------------------------------------------------*)
Request == [type : {"read", "write"}, proc : n]

(*--------------------------------------------------------------------
  Initial state.
--------------------------------------------------------------------*)
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = << >>

(*--------------------------------------------------------------------
  Helper predicates.
--------------------------------------------------------------------*)
IsQueued(p) == \E r \in Queue : r.proc = p

CanRequest(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ ~IsQueued(p)

(*--------------------------------------------------------------------
  Action: a process requests read access.
--------------------------------------------------------------------*)
RequestRead(p) ==
    /\ CanRequest(p)
    /\ Queue' = Append(Queue, [type |-> "read", proc |-> p])
    /\ UNCHANGED << Readers, Writers >>

(*--------------------------------------------------------------------
  Action: a process requests write access.
--------------------------------------------------------------------*)
RequestWrite(p) ==
    /\ CanRequest(p)
    /\ Queue' = Append(Queue, [type |-> "write", proc |-> p])
    /\ UNCHANGED << Readers, Writers >>

(*--------------------------------------------------------------------
  Action: process the front of the queue.
--------------------------------------------------------------------*)
ProcessQueue ==
    /\ Queue # << >>
    /\ Writers = {}                                 \* no writer currently active
    /\ LET front == Head(Queue) IN
       \/ /\ front.type = "read"
          /\ Readers' = Readers \cup {front.proc}
          /\ Writers' = Writers
          /\ Queue'   = Tail(Queue)
       \/ /\ front.type = "write"
          /\ Readers = {}                         \* no readers while granting a write
          /\ Writers' = Writers \cup {front.proc}
          /\ Readers' = Readers
          /\ Queue'   = Tail(Queue)

(*--------------------------------------------------------------------
  Action: a process stops its current activity (reading or writing).
--------------------------------------------------------------------*)
Stop(p) ==
    /\ p \in Readers \/ p \in Writers
    /\ IF p \in Readers
          THEN /\ Readers' = Readers \ {p}
               /\ Writers' = Writers
          ELSE /\ Writers' = Writers \ {p}
               /\ Readers' = Readers
    /\ Queue' = Queue

(*--------------------------------------------------------------------
  Next-state relation.
--------------------------------------------------------------------*)
Next ==
    \/ \E p \in n : RequestRead(p)
    \/ \E p \in n : RequestWrite(p)
    \/ ProcessQueue
    \/ \E p \in n : Stop(p)

(*--------------------------------------------------------------------
  Specification.
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<Readers, Writers, Queue>>

(*--------------------------------------------------------------------
  Type correctness invariant.
--------------------------------------------------------------------*)
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Readers \cap Writers = {}
    /\ Queue \in Seq(Request)
    /\ \A r \in Queue :
          /\ r.type \in {"read", "write"}
          /\ r.proc \in n

(*--------------------------------------------------------------------
  Safety invariant: readers and writers never active together,
  and at most one writer.
--------------------------------------------------------------------*)
Safety ==
    /\ (Writers = {} \/ Readers = {})
    /\ Cardinality(Writers) <= 1

(*--------------------------------------------------------------------
  Liveness property: every process eventually reads and writes,
  and any active reader/writer eventually stops.
--------------------------------------------------------------------*)
Liveness ==
    /\ \A p \in n :
          <> (p \in Readers)               \* p eventually reads
       /\ <> (p \in Writers)               \* p eventually writes
       /\ [] (p \in Readers => <> (p \notin Readers))   \* readers eventually stop
       /\ [] (p \in Writers => <> (p \notin Writers))   \* writers eventually stop

====