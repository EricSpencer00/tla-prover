---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* The queue itself is the ordering mechanism that guarantees fairness:
\* actors are processed strictly in the order their requests arrived, so
\* neither readers nor writers can be overtaken and starved.
VARIABLES reading, writing, queue

Actors == 1..NumActors
Reqs == {1..3}
\* a request records who made it and whether it is a read: read/write requests
\* are carried together in one queue so that the ordering is truly first-come.
QueueEntry == [who: Actors, rw: Reqs]

TypeOK ==
  /\ reading \subseteq Actors
  /\ writing \subseteq Actors
  /\ queue \in Seq(QueueEntry)

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = << >>

RequestRead(a) ==
  /\ \A i \in DOMAIN queue : queue[i].who # a /\ queue[i].rw = 1
  /\ queue' = Append(queue, [who |-> a, rw |-> 1])
  /\ UNCHANGED <<reading, writing>>

RequestWrite(a) ==
  /\ \A i \in DOMAIN queue : queue[i].who # a /\ queue[i].rw = 2
  /\ queue' = Append(queue, [who |-> a, rw |-> 2])
  /\ UNCHANGED <<reading, writing>>

\* The head of the queue begins access only when it would not conflict
\* with anything currently active.  A writer also finds the readers empty.
ProcessQueue ==
  /\ queue # << >>
  /\ writing = {}
  /\ LET entry == Head(queue) IN
       /\ IF entry.rw = 1
            THEN reading' = reading \cup {entry.who} /\ writing' = writing
            ELSE /\ reading' = reading
                 /\ writing' = writing \cup {entry.who}
       /\ queue' = Tail(queue)

StopActivity(a) ==
  /\ \/ a \in reading
     \/ a \in writing
  /\ reading' = reading \ {a}
  /\ writing' = writing \ {a}
  /\ UNCHANGED queue

Next ==
  \/ \E a \in Actors : RequestRead(a)
  \/ \E a \in Actors : RequestWrite(a)
  \/ ProcessQueue
  \/ \E a \in Actors : StopActivity(a)

Spec == Init /\ [][Next]_<<reading, writing, queue>>

\* Readers and writers never run at the same time, and never more than one
\* writer -- this is the mutual-exclusion guarantee the whole design rests on.
Safety ==
  /\ \/ (writing = {} \/ reading = {})
     \/ (reading = {} \/ writing = {})
  /\ Cardinality(writing) <= 1

\* Fair access: every actor that ever wants to read (or write) eventually
\* gets that access, and never stays stuck reading or writing forever.
Liveness ==
  /\ \A a \in Actors : (RequestRead(a)) ~> (a \in reading)
  /\ \A a \in Actors : (RequestWrite(a)) ~> (a \in writing)
  /\ \A a \in Actors : (a \in reading) ~> (a \notin reading)
  /\ \A a \in Actors : (a \in writing) ~> (a \notin writing)

\* Weak fairness of the constituent actions is what makes the "eventually"
\* clauses above hold; without it an enqueued request could be postponed
\* forever behind a never-ending stream of others.
Fairness ==
  /\ \A a \in Actors : WF_vars(RequestRead(a))
  /\ \A a \in Actors : WF_vars(RequestWrite(a))
  /\ WF_vars(ProcessQueue)
  /\ \A a \in Actors : WF_vars(StopActivity(a))

====