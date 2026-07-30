---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

VARIABLES reading, writing, queue
vars == <<reading, writing, queue>>

Requests == [type : {"read", "write"}, who : 0..(NumActors - 1)]
ReqOf(req) == req.type

TypeOK ==
  /\ reading \subseteq (0..(NumActors - 1))
  /\ writing \subseteq (0..(NumActors - 1))
  /\ queue \in Seq(Requests)

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = << >>

RequestRead(p) ==
  /\ Len(queue) < 3
  /\ ~ \E i \in 1..Len(queue) : queue[i].who = p /\ queue[i].type = "read"
  /\ queue' = Append(queue, [type |-> "read", who |-> p])
  /\ UNCHANGED <<reading, writing>>

RequestWrite(p) ==
  /\ Len(queue) < 3
  /\ ~ \E i \in 1..Len(queue) : queue[i].who = p /\ queue[i].type = "write"
  /\ queue' = Append(queue, [type |-> "write", who |-> p])
  /\ UNCHANGED <<reading, writing>>

BeginAccess ==
  /\ queue # << >>
  /\ writing = {}
  /\ LET front == Head(queue) IN
       IF front.type = "read"
         THEN /\ reading' = reading \cup {front.who}
              /\ queue' = Tail(queue)
         ELSE /\ reading = {}
              /\ writing' = writing \cup {front.who}
              /\ queue' = Tail(queue)
  /\ UNCHANGED reading

StopActivity(p) ==
  /\ \/ p \in reading
     \/ p \in writing
  /\ reading' = reading \ {p}
  /\ writing' = writing \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in 0..(NumActors - 1) : RequestRead(p)
  \/ \E p \in 0..(NumActors - 1) : RequestWrite(p)
  \/ BeginAccess
  \/ \E p \in 0..(NumActors - 1) : StopActivity(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in 0..(NumActors - 1) : RequestRead(p))
  /\ WF_vars(\E p \in 0..(NumActors - 1) : RequestWrite(p))
  /\ WF_vars(BeginAccess)
  /\ WF_vars(\E p \in 0..(NumActors - 1) : StopActivity(p))

Safety ==
  /\ (writing # {}) => (reading = {})
  /\ (writing # {}) => (cardinality(writing) = 1)

Liveness ==
  /\ \A p \in 0..(NumActors - 1) : (p \in reading) ~> (p \notin reading)
  /\ \A p \in 0..(NumActors - 1) : (p \in writing) ~> (p \notin writing)

====