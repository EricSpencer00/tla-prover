---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANT NumActors

ASSUME NumActors \in Nat

Actors == 1..NumActors

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

TypeOK ==
  /\ reading \subseteq Actors
  /\ writing \subseteq Actors
  /\ \A i \in DOMAIN queue : queue[i].actor \in Actors /\ queue[i].rw \in {"r", "w"}

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = <<>>

RequestRead(a) ==
  /\ ( \A i \in DOMAIN queue : queue[i].actor # a )
  /\ queue' = Append(queue, [rw |-> "r", actor |-> a])
  /\ UNCHANGED <<reading, writing>>

RequestWrite(a) ==
  /\ ( \A i \in DOMAIN queue : queue[i].actor # a )
  /\ queue' = Append(queue, [rw |-> "w", actor |-> a])
  /\ UNCHANGED <<reading, writing>>

ProcessQueue ==
  /\ queue # <<>>
  /\ writing = {}
  /\ LET head == Head(queue) IN
       IF head.rw = "r" THEN
         reading' = reading \cup {head.actor}
         /\ writing' = {}
       ELSE IF reading = {} THEN
         reading' = {}
         /\ writing' = writing \cup {head.actor}
       ELSE
         reading' = reading
         /\ writing' = writing
       /\ queue' = Tail(queue)

StopReading(a) ==
  /\ a \in reading
  /\ reading' = reading \ {a}
  /\ UNCHANGED <<writing, queue>>

StopWriting(a) ==
  /\ a \in writing
  /\ writing' = writing \ {a}
  /\ UNCHANGED <<reading, queue>>

Next ==
  \/ \E a \in Actors : RequestRead(a) \/ RequestWrite(a) \/ StopReading(a) \/ StopWriting(a)
  \/ ProcessQueue

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E a \in Actors : RequestRead(a))
  /\ WF_vars(\E a \in Actors : RequestWrite(a))
  /\ WF_vars(ProcessQueue)
  /\ \A a \in Actors : WF_vars(StopReading(a)) /\ WF_vars(StopWriting(a))

Safety ==
  /\ ~(reading # {} /\ writing # {})
  /\ Cardinality(writing) <= 1

Liveness ==
  /\ \A a \in Actors : [][(\A p \in Actors : p # a => TRUE /\ a \in reading) \/ TRUE]_vars
  /\ \A a \in Actors : [][(\A p \in Actors : p # a => TRUE /\ a \in writing) \/ TRUE]_vars
  /\ \A a \in Actors : [][(\A p \in Actors : p # a => TRUE /\ a \notin reading) \/ TRUE]_vars
  /\ \A a \in Actors : [][(\A p \in Actors : p # a => TRUE /\ a \notin writing) \/ TRUE]_vars

====