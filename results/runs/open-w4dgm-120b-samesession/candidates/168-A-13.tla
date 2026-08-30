---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

VARIABLES reading, writing, queue

AllActors == 1..NumActors

TypeOK ==
  /\ reading \subseteq AllActors
  /\ writing \subseteq AllActors
  /\ queue \in Seq([act: {"read", "write"}, who: AllActors])

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = <<>>

RequestRead(a) ==
  /\ \A i \in 1..Len(queue) : queue[i].who # a
  /\ queue' = Append(queue, [act |-> "read", who |-> a])
  /\ UNCHANGED <<reading, writing>>

RequestWrite(a) ==
  /\ \A i \in 1..Len(queue) : queue[i].who # a
  /\ queue' = Append(queue, [act |-> "write", who |-> a])
  /\ UNCHANGED <<reading, writing>>

BeginService ==
  /\ Len(queue) > 0
  /\ writing = {}
  /\ LET r == Head(queue) IN
       \/ /\ r.act = "read"
          /\ r.who \notin reading
          /\ reading' = reading \cup {r.who}
          /\ queue' = Tail(queue)
          /\ UNCHANGED writing
       \/ /\ r.act = "write"
          /\ r.who \notin reading
          /\ reading = {}
          /\ writing' = writing \cup {r.who}
          /\ queue' = Tail(queue)
          /\ UNCHANGED reading
  /\ UNCHANGED <<>>

StopActivity(a) ==
  /\ (a \in reading \/ a \in writing)
  /\ reading' = reading \ {a}
  /\ writing' = writing \ {a}
  /\ UNCHANGED queue

Next ==
  \/ \E a \in AllActors : RequestRead(a)
  \/ \E a \in AllActors : RequestWrite(a)
  \/ BeginService
  \/ \E a \in AllActors : StopActivity(a)

Spec == Init /\ [][Next]_<<reading, writing, queue>>

Safety ==
  /\ (reading # {} => writing = {})
  /\ (writing # {} => reading = {})
  /\ \A a \in writing : \A b \in writing : a = b

Liveness ==
  /\ \A a \in AllActors : (a \in reading) ~> (a \notin reading)
  /\ \A a \in AllActors : (a \in writing) ~> (a \notin writing)

====