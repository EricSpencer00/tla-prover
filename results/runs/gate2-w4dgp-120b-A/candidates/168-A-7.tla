---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

ASSUME NumActors \in Nat /\ NumActors > 0

Actors == 1..NumActors

Queue == [mode : {"read", "write"}, actor : Actors]

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

\* The shared resource is never held by a reader and a writer at once, and the
\* queue gives first-come-first-served fairness between them.
TypeOK ==
  /\ reading \subseteq Actors
  /\ writing \subseteq Actors
  /\ \A i \in DOMAIN queue : queue[i] \in Queue

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = <<>>

\* An idle process joins the queue to read.
RequestRead(a) ==
  /\ \A i \in DOMAIN queue : queue[i].actor # a
  /\ queue' = Append(queue, [mode |-> "read", actor |-> a])
  /\ UNCHANGED <<reading, writing>>

\* An idle process joins the queue to write.
RequestWrite(a) ==
  /\ \A i \in DOMAIN queue : queue[i].actor # a
  /\ queue' = Append(queue, [mode |-> "write", actor |-> a])
  /\ UNCHANGED <<reading, writing>>

\* The head of the queue is admitted when it would not violate mutual exclusion.
ProcessHead ==
  /\ Len(queue) > 0
  /\ writing = {}
  /\ (queue[1].mode = "read" \/ reading = {})
  /\ LET h == queue[1] IN
       /\ IF h.mode = "read"
            THEN reading' = reading \cup {h.actor}
            ELSE reading' = reading
       /\ IF h.mode = "write"
            THEN writing' = writing \cup {h.actor}
            ELSE writing' = writing
       /\ queue' = Tail(queue)

\* A reader or writer voluntarily releases the resource.
StopActivity(a) ==
  /\ (a \in reading \/ a \in writing)
  /\ reading' = reading \ {a}
  /\ writing' = writing \ {a}
  /\ UNCHANGED queue

Next ==
  \/ \E a \in Actors : RequestRead(a)
  \/ \E a \in Actors : RequestWrite(a)
  \/ ProcessHead
  \/ \E a \in Actors : StopActivity(a)

Spec ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(\E a \in Actors : RequestRead(a))
  /\ WF_vars(\E a \in Actors : RequestWrite(a))
  /\ WF_vars(ProcessHead)
  /\ WF_vars(\E a \in Actors : StopActivity(a))

\* Readers and writers are never active together, and writing is mutually exclusive.
Safety ==
  /\ (writing # {} => reading = {})
  /\ \A a \in Actors, b \in Actors : (a \in writing /\ b \in writing) => a = b

\* Every process eventually gets to read, and every process eventually gets to write.
Liveness ==
  /\ \A a \in Actors : (a \in reading) ~> (a \notin reading)
  /\ \A a \in Actors : (a \in writing) ~> (a \notin writing)

====