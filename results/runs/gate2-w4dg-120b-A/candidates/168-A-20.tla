---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Actor == 1..NumActors
ReqType == {"read", "write"}
Request == [type : ReqType, actor : Actor]

VARIABLES readers, writers, queue
vars == <<readers, writers, queue>>

TypeOK ==
  /\ readers \subseteq Actor
  /\ writers \subseteq Actor
  /\ queue \in Seq(Request)

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = << >>

RequestRead(a) ==
  /\ queue' = Append(queue, [type |-> "read", actor |-> a])
  /\ UNCHANGED <<readers, writers>>

RequestWrite(a) ==
  /\ queue' = Append(queue, [type |-> "write", actor |-> a])
  /\ UNCHANGED <<readers, writers>>

ProcessQueue ==
  /\ queue # << >>
  /\ writers = {}
  /\ LET front == Head(queue) IN
       IF front.type = "read" THEN
         /\ readers' = readers \cup {front.actor}
         /\ writers' = writers
       ELSE
         /\ writers' = IF readers = {} THEN writers \cup {front.actor} ELSE writers
         /\ readers' = readers
  /\ queue' = Tail(queue)

StopActivity(a) ==
  /\ \/ a \in readers
     \/ a \in writers
  /\ readers' = readers \ {a}
  /\ writers' = writers \ {a}
  /\ UNCHANGED queue

Next ==
  \/ \E a \in Actor : RequestRead(a)
  \/ \E a \in Actor : RequestWrite(a)
  \/ ProcessQueue
  \/ \E a \in Actor : StopActivity(a)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E a \in Actor : RequestRead(a))
  /\ WF_vars(\E a \in Actor : RequestWrite(a))
  /\ WF_vars(ProcessQueue)
  /\ WF_vars(\E a \in Actor : StopActivity(a))

Safety ==
  /\ writers = {}
     => readers \cap writers = {}
  /\ readers = {}
     => readers \cap writers = {}

Liveness ==
  /\ \A a \in Actor : (a \in readers) ~> (a \notin readers)
  /\ \A a \in Actor : (a \in writers) ~> (a \notin writers)

====