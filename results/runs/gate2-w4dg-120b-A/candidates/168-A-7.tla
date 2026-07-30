---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Actor == 1..NumActors
ReqKind == {"read", "write"}

VARIABLES readers, writers, queue
vars == <<readers, writers, queue>>

QueueReq == [kind: ReqKind, actor: Actor]

TypeOK ==
  /\ readers \subseteq Actor
  /\ writers \subseteq Actor
  /\ queue \in Seq(QueueReq)

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = << >>

RequestRead(a) ==
  /\ \A i \in 1..Len(queue) : ~(queue[i].kind = "read" /\ queue[i].actor = a)
  /\ queue' = Append(queue, [kind |-> "read", actor |-> a])
  /\ UNCHANGED <<readers, writers>>

RequestWrite(a) ==
  /\ \A i \in 1..Len(queue) : ~(queue[i].kind = "write" /\ queue[i].actor = a)
  /\ queue' = Append(queue, [kind |-> "write", actor |-> a])
  /\ UNCHANGED <<readers, writers>>

BeginAccess ==
  /\ Len(queue) > 0
  /\ writers = {}
  /\ LET front == Head(queue) IN
       /\ IF front.kind = "read"
            THEN readers' = readers \cup {front.actor} /\ writers' = writers
            ELSE IF front.kind = "write" /\ readers = {}
              THEN writers' = writers \cup {front.actor} /\ readers' = readers
              ELSE readers' = readers /\ writers' = writers
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
  \/ BeginAccess
  \/ \E a \in Actor : StopActivity(a)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E a \in Actor : RequestRead(a))
  /\ WF_vars(\E a \in Actor : RequestWrite(a))
  /\ WF_vars(BeginAccess)
  /\ WF_vars(\E a \in Actor : StopActivity(a))

Safety ==
  /\ (writers # {} => readers = {})
  /\ Cardinality(writers) <= 1

Liveness ==
  /\ \A a \in Actor : readers = {} ~> readers \cup {a}
  /\ \A a \in Actor : writers = {} ~> writers \cup {a}
  /\ \A a \in Actor : (a \in readers) ~> (a \notin readers)
  /\ \A a \in Actor : (a \in writers) ~> (a \notin writers)

====