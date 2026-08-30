---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

Actors == 1..NumActors
NONE == "none"

Type == {"read", "write"}

VARIABLES reading, writing, queue
vars == <<reading, writing, queue>>

Mode == CHOOSE a \in Actors : TRUE

Reqs == [actor : Actors, typ : Type]

Range(q) == {q[i] : i \in DOMAIN q}
Queued(a) == \E i \in DOMAIN queue : queue[i].actor = a

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = <<>>

RequestRead(a) ==
  /\ ~Queued(a)
  /\ queue' = Append(queue, [actor |-> a, typ |-> "read"])
  /\ UNCHANGED <<reading, writing>>

RequestWrite(a) ==
  /\ ~Queued(a)
  /\ queue' = Append(queue, [actor |-> a, typ |-> "write"])
  /\ UNCHANGED <<reading, writing>>

BeginAccess ==
  /\ queue # <<>>
  /\ writing = {}
  /\ LET pkt == Head(queue) IN
       /\ IF pkt.typ = "read" THEN reading' = reading \cup {pkt.actor} ELSE reading' = reading
       /\ IF pkt.typ = "write" /\ reading = {} THEN writing' = writing \cup {pkt.actor} ELSE writing' = writing
  /\ queue' = Tail(queue)

Stop ==
  /\ \/ \E a \in reading : reading' = reading \ {a} /\ UNCHANGED <<writing, queue>>
     \/ \E a \in writing : writing' = writing \ {a} /\ UNCHANGED <<reading, queue>>

Next ==
  \/ \E a \in Actors : RequestRead(a) \/ RequestWrite(a)
  \/ BeginAccess
  \/ Stop

Spec == Init /\ [][Next]_vars
  /\ \A a \in Actors : WF_vars(RequestRead(a)) /\ WF_vars(RequestWrite(a))
  /\ WF_vars(BeginAccess) /\ WF_vars(Stop)

TypeOK ==
  /\ reading \subseteq Actors
  /\ writing \subseteq Actors
  /\ \A i \in DOMAIN queue : queue[i] \in Reqs

Safety ==
  /\ ~(reading \cap writing = {})
  /\ \A a, b \in writing : a = b

Liveness ==
  /\ \A a \in Actors : (a \in reading) ~> (a \notin reading)
  /\ \A a \in Actors : (a \in writing) ~> (a \notin writing)

====