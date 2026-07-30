---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

VARIABLES readers, writers, queue
vars == <<readers, writers, queue>>

Waiting == [kind : {"read", "write"}, pid : 1..NumActors]

TypeOK ==
  /\ readers \subseteq (1..NumActors)
  /\ writers \subseteq (1..NumActors)
  /\ queue \in Seq(Waiting)

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

RequestRead(p) ==
  /\ ~ \E i \in 1..Len(queue) : queue[i].pid = p /\ queue[i].kind = "read"
  /\ queue' = Append(queue, [kind |-> "read", pid |-> p])
  /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
  /\ ~ \E i \in 1..Len(queue) : queue[i].pid = p /\ queue[i].kind = "write"
  /\ queue' = Append(queue, [kind |-> "write", pid |-> p])
  /\ UNCHANGED <<readers, writers>>

ProcessQueue ==
  /\ Len(queue) > 0
  /\ writers = {}
  /\ LET front == Head(queue) IN
       IF front.kind = "read" THEN
         readers' = readers \cup {front.pid}
       ELSE IF writers = {} /\ readers = {} THEN
         writers' = writers \cup {front.pid}
       ELSE
         /\ readers' = readers
         /\ writers' = writers
       /\ UNCHANGED <<readers, writers>>
  /\ queue' = Tail(queue)

StopActivity(p) ==
  /\ \/ p \in readers
     \/ p \in writers
  /\ readers' = readers \ {p}
  /\ writers' = writers \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in 1..NumActors : RequestRead(p)
  \/ \E p \in 1..NumActors : RequestWrite(p)
  \/ ProcessQueue
  \/ \E p \in 1..NumActors : StopActivity(p)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..NumActors : RequestRead(p))
  /\ WF_vars(\E p \in 1..NumActors : RequestWrite(p))
  /\ WF_vars(ProcessQueue)
  /\ WF_vars(\E p \in 1..NumActors : StopActivity(p))

Safety ==
  /\ (writers # {} => readers = {})
  /\ (readers # {} => writers = {})
  /\ Cardinality(writers) <= 1

Liveness ==
  /\ \A p \in 1..NumActors : (p \in readers) ~> (p \notin readers)
  /\ \A p \in 1..NumActors : (p \in writers) ~> (p \notin writers)

====