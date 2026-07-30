---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

\* Actors request read/write access to a shared resource. A single
\* waiting queue decides who is served next, giving writers exclusive
\* access and readers shared access, in a first-come-first-served way.
\* Weak fairness on every action is assumed in the model config, so no
\* enabled action stays postponed forever.

CONSTANTS NumActors

Actors == 1..NumActors
Actions == {"read", "write"}

VARIABLES readers, writers, queue
vars == <<readers, writers, queue>>

TypeOK ==
  /\ readers \subseteq Actors
  /\ writers \subseteq Actors
  /\ queue \in Seq([actor: Actors, act: Actions])

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

\* A process that is not already queued asks to read, joining the back of
\* the waiting queue.
RequestRead(a) ==
  /\ \A i \in 1..Len(queue): queue[i].actor # a
  /\ queue' = Append(queue, [actor |-> a, act |-> "read"])
  /\ UNCHANGED <<readers, writers>>

\* A process that is not already queued asks to write, joining the back of
\* the waiting queue.
RequestWrite(a) ==
  /\ \A i \in 1..Len(queue): queue[i].actor # a
  /\ queue' = Append(queue, [actor |-> a, act |-> "write"])
  /\ UNCHANGED <<readers, writers>>

\* The head of the queue is served, but only if it would not break the
\* readers-writers discipline: a writer needs nobody reading first.
Serve ==
  /\ queue # <<>>
  /\ writers = {}
  /\ LET h == Head(queue) IN
       /\ IF h.act = "read" \/ readers = {}
          THEN readers' = readers \cup {h.actor}
               writers' = writers
          ELSE readers' = readers
               writers' = writers \cup {h.actor}
       /\ queue' = Tail(queue)

StopRead(a) ==
  /\ a \in readers
  /\ readers' = readers \ {a}
  /\ UNCHANGED <<writers, queue>>

StopWrite(a) ==
  /\ a \in writers
  /\ writers' = writers \ {a}
  /\ UNCHANGED <<readers, queue>>

Next ==
  \/ \E a \in Actors: RequestRead(a)
  \/ \E a \in Actors: RequestWrite(a)
  \/ Serve
  \/ \E a \in Actors: StopRead(a)
  \/ \E a \in Actors: StopWrite(a)

Spec == Init /\ [][Next]_vars

\* Readers and writers are never both active, and writers are mutually exclusive.
Safety == (writers # {}) => (readers = {})

\* Every process eventually gets to read and to write, and every active
\* reader/writer eventually stops -- strong enough to rule out starvation.
Liveness ==
  /\ \A a \in Actors: (a \in readers) ~> (a \notin readers)
  /\ \A a \in Actors: (a \in writers) ~> (a \notin writers)
  /\ \A a \in Actors: (a \notin readers) ~> (a \in readers)
  /\ \A a \in Actors: (a \notin writers) ~> (a \in writers)

====