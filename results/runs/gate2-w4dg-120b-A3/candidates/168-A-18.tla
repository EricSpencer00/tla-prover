---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* Access types and the number of actors are injected by the .cfg via substitution.
AccessKinds == { "read", "write" }
\* n is the finite set of actors the .cfg substitutes for NumActors.
n == 0 .. (NumActors - 1)

VARIABLES reading, writing, queue

vars == << reading, writing, queue >>

Requests == [ kind : AccessKinds, who : n ]

TypeOK ==
  /\ reading \subseteq n
  /\ writing \subseteq n
  /\ queue \in Seq(Requests)
  /\ \A i \in DOMAIN queue : queue[i].who \notin reading

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = << >>

RequestRead(a) ==
  /\ \A i \in DOMAIN queue : queue[i].who # a
  /\ queue' = Append(queue, [ kind |-> "read", who |-> a ])
  /\ UNCHANGED << reading, writing >>

RequestWrite(a) ==
  /\ \A i \in DOMAIN queue : queue[i].who # a
  /\ queue' = Append(queue, [ kind |-> "write", who |-> a ])
  /\ UNCHANGED << reading, writing >>

\* The queue head is admitted only when it would not violate mutual exclusion.
ProcessQueue ==
  /\ queue # << >>
  /\ writing = {}
  /\ LET req == Head(queue) IN
       \/ /\ req.kind = "read"
            /\ reading' = reading \cup { req.who }
            /\ writing' = writing
       \/ /\ req.kind = "write"
            /\ reading = {}
            /\ reading' = {}
            /\ writing' = { req.who }
  /\ queue' = Tail(queue)

StopActivity(a) ==
  /\ \/ a \in reading
     \/ a \in writing
  /\ reading' = reading \ { a }
  /\ writing' = writing \ { a }
  /\ UNCHANGED queue

Next ==
  \/ \E a \in n : RequestRead(a) \/ RequestWrite(a) \/ StopActivity(a)
  \/ ProcessQueue

Spec == Init /\ [][Next]_vars
        /\ WF_vars(ProcessQueue)
        /\ \A a \in n : WF_vars(RequestRead(a)) /\ WF_vars(RequestWrite(a)) /\ WF_vars(StopActivity(a))

\* Safety: readers and writers are never both active, and only one writer exists.
Safety ==
  /\ (writing # {} => reading = {})
  /\ Cardinality(writing) <= 1

\* Liveness: every actor both reads and writes and always stops once active.
Liveness ==
  /\ \A a \in n : (a \in reading) ~> (a \notin reading)
  /\ \A a \in n : (a \in writing) ~> (a \notin writing)
  /\ \A a \in n : (a \in reading) ~> (a \in writing)
  /\ \A a \in n : (a \in writing) ~> (a \in reading)

====