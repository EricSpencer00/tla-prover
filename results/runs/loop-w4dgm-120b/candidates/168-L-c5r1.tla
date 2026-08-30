---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

Ring == 1..NumActors

Requests == [type : {"r", "w"}, actor : Ring]

TypeOK ==
  /\ reading \subseteq Ring
  /\ writing \subseteq Ring
  /\ queue \in Seq(Requests)

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = << >>

RequestRead(i) ==
  /\ ~ \E k \in 1..Len(queue) : queue[k].actor = i
  /\ queue' = Append(queue, [type |-> "r", actor |-> i])
  /\ UNCHANGED <<reading, writing>>

RequestWrite(i) ==
  /\ ~ \E k \in 1..Len(queue) : queue[k].actor = i
  /\ queue' = Append(queue, [type |-> "w", actor |-> i])
  /\ UNCHANGED <<reading, writing>>

ProcessQueue ==
  /\ queue # << >>
  /\ writing = {}
  /\ LET req == Head(queue)
     IN IF req.type = "r"
        THEN reading' = reading \cup {req.actor}
        ELSE IF reading = {}
             THEN writing' = writing \cup {req.actor}
             ELSE UNCHANGED <<reading, writing>>
  /\ queue' = Tail(queue)

StopActivity(i) ==
  /\ \/ i \in reading
     \/ i \in writing
  /\ reading' = reading \ {i}
  /\ writing' = writing \ {i}
  /\ UNCHANGED queue

Next ==
  \/ \E i \in Ring: RequestRead(i) \/ RequestWrite(i) \/ StopActivity(i)
  \/ ProcessQueue

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in Ring: WF_vars(RequestRead(i)) /\ WF_vars(RequestWrite(i)) /\ WF_vars(StopActivity(i))
  /\ WF_vars(ProcessQueue)

Safety ==
  /\ (writing # {}) => (reading = {})
  /\ (reading # {}) => (writing = {})
  /\ \A a, b \in writing: a = b

Liveness ==
  /\ \A i \in Ring: (i \notin reading) ~> (i \in reading)
  /\ \A i \in Ring: (i \notin writing) ~> (i \in writing)
  /\ \A i \in Ring: (i \in reading) ~> (i \notin reading)
  /\ \A i \in Ring: (i \in writing) ~> (i \notin writing)

====