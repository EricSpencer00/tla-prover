---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* The shared-resource state: who is reading, who is writing, and the waiting queue.
VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

Requests == [type: {"read", "write"}, actor: NumActors]

TypeOK ==
  /\ readers \subseteq NumActors
  /\ writers \subseteq NumActors
  /\ queue \in Seq(Requests)

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

\* Readers and writers are mutually exclusive: they are never both active.
MutualExclusion ==
  /\ (writers # {} => readers = {})
  /\ (readers # {} => writers = {})
  /\ Cardinality(writers) <= 1

\* Either branch of the exclusive-access test may fire while the queue is non-empty,
\* and writers are blocked until every reader has finished.
BeginReadOrWrite ==
  /\ Len(queue) > 0
  /\ writers = {}
  /\ LET h == Head(queue) IN
       IF h.type = "read" THEN
         readers' = readers \cup {h.actor}
       ELSE
         IF readers = {} THEN writers' = writers \cup {h.actor} ELSE writers' = writers
       /\ queue' = Tail(queue)
  /\ UNCHANGED <<readers, writers>>

RequestRead(a) ==
  /\ ~ \E i \in DOMAIN queue : queue[i].actor = a /\ queue[i].type = "read"
  /\ queue' = Append(queue, [type |-> "read", actor |-> a])
  /\ UNCHANGED <<readers, writers>>

RequestWrite(a) ==
  /\ ~ \E i \in DOMAIN queue : queue[i].actor = a /\ queue[i].type = "write"
  /\ queue' = Append(queue, [type |-> "write", actor |-> a])
  /\ UNCHANGED <<readers, writers>>

StopActivity(a) ==
  /\ readers' = readers \ {a}
  /\ writers' = writers \ {a}
  /\ UNCHANGED <<queue>>

Next ==
  \/ \E a \in NumActors : RequestRead(a) \/ RequestWrite(a) \/ StopActivity(a)
  \/ BeginReadOrWrite

Spec == Init /\ [][Next]_vars
    /\ \A a \in NumActors :
         /\ WF_vars(RequestRead(a))
         /\ WF_vars(RequestWrite(a))
         /\ WF_vars(StopActivity(a))
    /\ WF_vars(BeginReadOrWrite)

EventuallyRead == \A a \in NumActors : <>(a \in readers)
EventuallyWrite == \A a \in NumActors : <>(a \in writers)
AllReadersEventuallyStop == \A a \in NumActors : (a \in readers) ~> (a \notin readers)
AllWritersEventuallyStop == \A a \in NumActors : (a \in writers) ~> (a \notin writers)

Safety == MutualExclusion
Liveness == EventuallyRead /\ EventuallyWrite /\ AllReadersEventuallyStop /\ AllWritersEventuallyStop
====