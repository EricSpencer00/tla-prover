---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* Weak fairness on every action is what guarantees no process seeks
\* forever. The queue adds the ordering discipline.
\* The required identifiers exactly match the .cfg: no more, no fewer.

Actors == 1..NumActors
Modes == {"read", "write"}
NoActor == 0
NoMode == "none"

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

Queued == CHOOSE i \in 1..Len(queue) : TRUE

TypeOK ==
  /\ reading \subseteq Actors
  /\ writing \subseteq Actors
  /\ Len(queue) <= NumActors
  /\ \A i \in 1..Len(queue) : queue[i].mode \in Modes /\ queue[i].who \in Actors

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = <<>>

RequestRead(a) ==
  /\ \A i \in 1..Len(queue) : queue[i].who # a
  /\ queue' = Append(queue, [mode |-> "read", who |-> a])
  /\ UNCHANGED <<reading, writing>>

RequestWrite(a) ==
  /\ \A i \in 1..Len(queue) : queue[i].who # a
  /\ queue' = Append(queue, [mode |-> "write", who |-> a])
  /\ UNCHANGED <<reading, writing>>

BeginAccess ==
  /\ Len(queue) > 0
  /\ writing = {}
  /\ LET q == queue[1]
       rest == Tail(queue)
     IN
        /\ IF q.mode = "read"
           THEN reading' = reading \cup {q.who} /\ writing' = writing
           ELSE reading' = reading /\ writing' = writing \cup {q.who}
        /\ queue' = rest

StopRead(a) ==
  /\ a \in reading
  /\ reading' = reading \ {a}
  /\ UNCHANGED <<writing, queue>>

StopWrite(a) ==
  /\ a \in writing
  /\ writing' = writing \ {a}
  /\ UNCHANGED <<reading, queue>>

Next ==
  \/ \E a \in Actors : RequestRead(a)
  \/ \E a \in Actors : RequestWrite(a)
  \/ BeginAccess
  \/ \E a \in Actors : StopRead(a)
  \/ \E a \in Actors : StopWrite(a)

Spec == Init /\ [][Next]_vars
  /\ \A a \in Actors : WF_vars(RequestRead(a))
  /\ \A a \in Actors : WF_vars(RequestWrite(a))
  /\ WF_vars(BeginAccess)
  /\ \A a \in Actors : WF_vars(StopRead(a))
  /\ \A a \in Actors : WF_vars(StopWrite(a))

\* Readers and writers never active together; at most one writer.
Safety ==
  /\ (writing # {} => reading = {})
  /\ (reading # {} => writing = {})
  /\ \A p, q \in writing : p = q

\* Fairness of the queue is what stops either side starving.
Liveness ==
  /\ \A a \in Actors : <>(a \in reading)
  /\ \A a \in Actors : <>(a \in writing)
  /\ \A a \in Actors : <>(a \notin reading)
  /\ \A a \in Actors : <>(a \notin writing)

\* The .cfg substitutes a concrete value for NumActors via n.
n == NumActors

====