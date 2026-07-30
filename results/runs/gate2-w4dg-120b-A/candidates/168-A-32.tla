---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* Actors request read or write access through a first-come-first-served queue.
\* Because a writer is admitted only when no reader holds the resource, readers
\* and writers are never active at the same time (the fairness guarantee).
\* Despite the queue, no actor is starved: every actor eventually reads and writes.

\* Queue elements record who made the request and whether it is for reading or writing.
Requests == [proc: 1..NumActors, kind: {"read", "write"}]

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

TypeOK ==
  /\ reading \subseteq (1..NumActors)
  /\ writing \subseteq (1..NumActors)
  /\ queue \in Seq(Requests)

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = << >>

\* A process that is not already waiting to read joins the end of the queue.
RequestRead(p) ==
  /\ \A i \in 1..Len(queue): queue[i].proc # p
  /\ queue' = Append(queue, [proc |-> p, kind |-> "read"])
  /\ UNCHANGED <<reading, writing>>

\* A process that is not already waiting to write joins the end of the queue.
RequestWrite(p) ==
  /\ \A i \in 1..Len(queue): queue[i].proc # p
  /\ queue' = Append(queue, [proc |-> p, kind |-> "write"])
  /\ UNCHANGED <<reading, writing>>

\* The queue is processed from the front. A read request always admits the actor.
\* A write request admits the actor only if no one is currently reading.
Grant ==
  /\ queue # << >>
  /\ writing = {}
  /\ LET head == Head(queue) IN
       IF head.kind = "read" THEN
         /\ reading' = reading \cup {head.proc}
         /\ queue' = Tail(queue)
         /\ UNCHANGED writing
       ELSE
         /\ reading = {}
         /\ writing' = {head.proc}
         /\ queue' = Tail(queue)
         /\ UNCHANGED reading

Stop(p) ==
  /\ \/ p \in reading
     \/ p \in writing
  /\ reading' = reading \ {p}
  /\ writing' = writing \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in 1..NumActors: RequestRead(p)
  \/ \E p \in 1..NumActors: RequestWrite(p)
  \/ Grant
  \/ \E p \in 1..NumActors: Stop(p)

Spec == Init /\ [][Next]_vars

\* Readers and writers are never active at the same time.
Safety == (writing # {}) => (reading = {}) /\ (writing \cap reading = {})

\* Both readers and writers eventually get a turn, and every active actor eventually stops.
Liveness ==
  /\ \A p \in 1..NumActors: (p \in reading) ~> (p \in reading)
  /\ \A p \in 1..NumActors: (p \in writing) ~> (p \in writing)
  /\ \A p \in 1..NumActors: (p \in reading) ~> (p \notin reading)
  /\ \A p \in 1..NumActors: (p \in writing) ~> (p \notin writing)

====