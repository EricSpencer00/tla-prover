---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Actors == 1..NumActors
Modes == {"read", "write"}

VARIABLES reading, writing, queue
vars == <<reading, writing, queue>>

Request == [mode: Modes, actor: Actors]

TypeOK ==
  /\ reading \subseteq Actors
  /\ writing \subseteq Actors
  /\ queue \in Seq(Request)

\* Readers and writers never act at the same time; also at most one writer.
Safety ==
  /\ (writing # {} => reading = {})
  /\ (reading # {} => writing = {})
  /\ Cardinality(writing) <= 1

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = <<>>

RequestRead(a) ==
  /\ \A i \in 1..Len(queue): ~(queue[i].mode = "read" /\ queue[i].actor = a)
  /\ queue' = Append(queue, [mode |-> "read", actor |-> a])
  /\ UNCHANGED <<reading, writing>>

RequestWrite(a) ==
  /\ \A i \in 1..Len(queue): ~(queue[i].mode = "write" /\ queue[i].actor = a)
  /\ queue' = Append(queue, [mode |-> "write", actor |-> a])
  /\ UNCHANGED <<reading, writing>>

ProcessQueued ==
  /\ Len(queue) > 0
  /\ writing = {}
  /\ IF queue[1].mode = "read" THEN
       /\ reading' = reading \cup {queue[1].actor}
       /\ UNCHANGED writing
     ELSE
       /\ reading = {}
       /\ writing' = writing \cup {queue[1].actor}
       /\ UNCHANGED reading
  /\ queue' = Tail(queue)

StopActivity(a) ==
  /\ (a \in reading \/ a \in writing)
  /\ reading' = reading \ {a}
  /\ writing' = writing \ {a}
  /\ UNCHANGED queue

Next ==
  \/ \E a \in Actors: RequestRead(a)
  \/ \E a \in Actors: RequestWrite(a)
  \/ ProcessQueued
  \/ \E a \in Actors: StopActivity(a)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E a \in Actors: RequestRead(a))
  /\ WF_vars(\E a \in Actors: RequestWrite(a))
  /\ WF_vars(ProcessQueued)
  /\ \A a \in Actors: WF_vars(StopActivity(a))

\* Every actor eventually gets to read and eventually gets to write.
Liveness ==
  /\ \A a \in Actors: <>(a \in reading)
  /\ \A a \in Actors: <>(a \in writing)
  /\ \A a \in Actors: [](a \in reading => <>(a \notin reading))
  /\ \A a \in Actors: [](a \in writing => <>(a \notin writing))

====