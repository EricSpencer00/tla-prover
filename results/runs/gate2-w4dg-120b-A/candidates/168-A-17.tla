---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

Actors == 1 .. NumActors
Direction == {"read", "write"}
Request == [dir: Direction, who: Actors]

VARIABLES reading, writing, queue
vars == <<reading, writing, queue>>

TypeOK ==
  /\ reading \subseteq Actors
  /\ writing \subseteq Actors
  /\ queue \in Seq(Request)

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = <<>>

RequestRead == \E a \in Actors :
  /\ ~ \E i \in 1..Len(queue) : queue[i].who = a /\ queue[i].dir = "read"
  /\ queue' = Append(queue, [dir |-> "read", who |-> a])
  /\ UNCHANGED <<reading, writing>>

RequestWrite == \E a \in Actors :
  /\ ~ \E i \in 1..Len(queue) : queue[i].who = a /\ queue[i].dir = "write"
  /\ queue' = Append(queue, [dir |-> "write", who |-> a])
  /\ UNCHANGED <<reading, writing>>

StartRead == \E a \in Actors :
  /\ queue # <<>>
  /\ writing = {}
  /\ queue[1].dir = "read"
  /\ queue[1].who = a
  /\ reading' = reading \cup {a}
  /\ queue' = Tail(queue)
  /\ UNCHANGED writing

StartWrite == \E a \in Actors :
  /\ queue # <<>>
  /\ writing = {}
  /\ reading = {}
  /\ queue[1].dir = "write"
  /\ queue[1].who = a
  /\ writing' = {a}
  /\ queue' = Tail(queue)
  /\ UNCHANGED reading

StopActivity == \E a \in Actors :
  /\ (a \in reading \/ a \in writing)
  /\ reading' = reading \ {a}
  /\ writing' = writing \ {a}
  /\ UNCHANGED queue

Next ==
  \/ RequestRead \/ RequestWrite \/ StartRead \/ StartWrite \/ StopActivity

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(RequestRead)
  /\ WF_vars(RequestWrite)
  /\ WF_vars(StartRead)
  /\ WF_vars(StartWrite)
  /\ WF_vars(StopActivity)

Safety ==
  /\ (writing # {} => reading = {})
  /\ \A a, b \in Actors : ~(a \in writing /\ b \in writing /\ a # b)

Liveness ==
  /\ \A a \in Actors : (a \in reading) ~> (a \notin reading)
  /\ \A a \in Actors : (a \in writing) ~> (a \notin writing)

====