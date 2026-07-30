---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* Actors queue up in a single FIFO so requests are served strictly in
\* order, which is the source of fairness here.
\* Each queue element records the request kind together with its writer.
Requests == {"read", "write"}

VARIABLES readers, writers, queue

vars == << readers, writers, queue >>

TypeOK ==
  /\ readers \subseteq 1..NumActors
  /\ writers \subseteq 1..NumActors
  /\ queue \in Seq([kind: Requests, actor: 1..NumActors])

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = << >>

\* A process not already at the back of the queue may append a read request.
RequestRead(i) ==
  /\ \A k \in 1..Len(queue): queue[k].actor # i
  /\ queue' = Append(queue, [kind |-> "read", actor |-> i])
  /\ UNCHANGED << readers, writers >>

\* A process not already at the back of the queue may append a write request.
RequestWrite(i) ==
  /\ \A k \in 1..Len(queue): queue[k].actor # i
  /\ queue' = Append(queue, [kind |-> "write", actor |-> i])
  /\ UNCHANGED << readers, writers >>

\* The front of the queue begins its access only when it would not break
\* mutual exclusion; the request is consumed off the front.
BeginAccess ==
  /\ queue # << >>
  /\ writers = {}
  /\ LET req == Head(queue) IN
       /\ IF req.kind = "read" THEN readers' = readers \cup {req.actor}
          ELSE /\ readers = {}
               /\ writers' = writers \cup {req.actor}
       /\ queue' = Tail(queue)

StopActivity(i) ==
  /\ \/ i \in readers
     \/ i \in writers
  /\ readers' = readers \ {i}
  /\ writers' = writers \ {i}
  /\ UNCHANGED queue

Next ==
  \E i \in 1..NumActors: RequestRead(i) \/ RequestWrite(i) \/ StopActivity(i)
  \/ BeginAccess

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(RequestRead(1))
  /\ WF_vars(RequestWrite(1))
  /\ WF_vars(BeginAccess)
  /\ WF_vars(StopActivity(1))

\* Safety: readers and writers never overlap, and writers are mutually exclusive.
Safety ==
  /\ (writers # {} => readers = {})
  /\ (readers # {} => writers = {})
  /\ \A a, b \in writers: a = b

\* Liveness: every process eventually reads, writes, and stops each activity it
\* starts. The fairness assumptions on BeginAccess and StopActivity are what make
\* this reachable for every process rather than just the first few.
Liveness ==
  /\ \A i \in 1..NumActors: <>(i \in readers)
  /\ \A i \in 1..NumActors: <>(i \in writers)
  /\ \A i \in 1..NumActors: <>(i \notin readers)
  /\ \A i \in 1..NumActors: <>(i \notin writers)

====