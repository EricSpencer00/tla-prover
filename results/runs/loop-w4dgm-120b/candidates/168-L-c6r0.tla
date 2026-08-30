---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* Readers-writers concurrency control with a fair request queue.
\* n is the number of processes in the system; the queue gives
\* first-come-first-served fairness, preventing starvation.
Actors == 1..NumActors
MaxQ == 2
n == NumActors

VARIABLES readers, writers, queue
vars == <<readers, writers, queue>>

TypeOK ==
  /\ readers \subseteq Actors
  /\ writers \subseteq Actors
  /\ queue \in Seq([kind: {"read", "write"}, actor: Actors])

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

\* A process requests read access (joined to the back of the queue).
RequestRead(a) ==
  /\ Len(queue) < MaxQ
  /\ \A i \in 1..Len(queue): queue[i].actor # a
  /\ queue' = Append(queue, [kind |-> "read", actor |-> a])
  /\ UNCHANGED <<readers, writers>>

\* A process requests write access (joined to the back of the queue).
RequestWrite(a) ==
  /\ Len(queue) < MaxQ
  /\ \A i \in 1..Len(queue): queue[i].actor # a
  /\ queue' = Append(queue, [kind |-> "write", actor |-> a])
  /\ UNCHANGED <<readers, writers>>

\* The head of the queue begins access, but only when the two groups stay disjoint.
Grant ==
  /\ Len(queue) > 0
  /\ writers = {}
  /\ LET req == Head(queue) IN
       /\ IF req.kind = "read" \/ Cardinality(readers) = 0
          THEN readers' = readers \cup {req.actor}
          ELSE readers' = readers
       /\ writers' = IF req.kind = "write" /\ Cardinality(readers) = 0
                    THEN writers \cup {req.actor} ELSE writers
  /\ queue' = Tail(queue)

\* Any active reader or writer may voluntarily stop.
Stop(a) ==
  \/ (a \in readers /\ readers' = readers \ {a})
  \/ (a \in writers /\ writers' = writers \ {a})
  /\ UNCHANGED <<queue>>

\* A reading process eventually stops.
StopRead == \E a \in Actors: Stop(a)

\* A writing process eventually stops.
StopWrite == \E a \in Actors: Stop(a)

\* A process eventually gets to read.
EventuallyRead == \E a \in Actors: RequestRead(a) /\ Stop(a)

\* A process eventually gets to write.
EventuallyWrite == \E a \in Actors: RequestWrite(a) /\ Stop(a)

Next ==
  \/ \E a \in Actors: RequestRead(a)
  \/ \E a \in Actors: RequestWrite(a)
  \/ Grant
  \/ \E a \in Actors: Stop(a)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(StopRead)
  /\ WF_vars(StopWrite)
  /\ SF_vars(EventuallyRead)
  /\ SF_vars(EventuallyWrite)

\* No reading while any process is writing, and vice versa: the two groups are disjoint.
Safety == readers \cap writers = {}
Liveness == (\A a \in Actors: StopRead) /\ (\A a \in Actors: StopWrite)
====