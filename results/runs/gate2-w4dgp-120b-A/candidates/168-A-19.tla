---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Ops == {"read", "write"}

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

\* The waiting queue carries both the requesting process and its intent (read or write),
\* so a writer request is not lost even though both actors and intents are drawn from
\* the same small domain.  Only one actor ever writes, and if anyone is writing no one reads.

TypeOK ==
  /\ readers \subseteq NumActors
  /\ writers \subseteq NumActors
  /\ queue \in Seq([actor : NumActors, op : Ops])

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

RequestRead(a) ==
  /\ \A i \in 1..Len(queue) : queue[i].actor # a
  /\ queue' = Append(queue, [actor |-> a, op |-> "read"])
  /\ UNCHANGED <<readers, writers>>

RequestWrite(a) ==
  /\ \A i \in 1..Len(queue) : queue[i].actor # a
  /\ queue' = Append(queue, [actor |-> a, op |-> "write"])
  /\ UNCHANGED <<readers, writers>>

ProcessQueue ==
  /\ Len(queue) > 0
  /\ writers = {}
  /\ LET head == Head(queue) IN
       /\ writers = {}
          => \/ (head.op = "read"  /\ readers' = readers \cup {head.actor})
               \/ (head.op = "write" /\ readers = {} /\ writers' = writers \cup {head.actor})
          /\ queue' = Tail(queue)
  /\ UNCHANGED readers

StopActivity(a) ==
  /\ \/ a \in readers
     \/ a \in writers
  /\ readers' = readers \ {a}
  /\ writers' = writers \ {a}
  /\ UNCHANGED queue

Next ==
  \/ \E a \in NumActors : RequestRead(a)
  \/ \E a \in NumActors : RequestWrite(a)
  \/ ProcessQueue
  \/ \E a \in NumActors : StopActivity(a)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E a \in NumActors : RequestRead(a))
  /\ WF_vars(\E a \in NumActors : RequestWrite(a))
  /\ WF_vars(ProcessQueue)
  /\ \A a \in NumActors : WF_vars(StopActivity(a))

\* Mutual exclusion: no readers while anyone writes, and writers are mutually exclusive.
Safety ==
  /\ (writers # {} => readers = {})
  /\ Cardinality(writers) <= 1
  /\ writers \subseteq NumActors

ReadersEventuallyActive ==
  \A a \in NumActors : (a \notin readers) ~> (a \in readers)

WritersEventuallyActive ==
  \A a \in NumActors : (a \notin writers) ~> (a \in writers)

ReadersEventuallyStop ==
  \A a \in NumActors : (a \in readers) ~> (a \notin readers)

WritersEventuallyStop ==
  \A a \in NumActors : (a \in writers) ~> (a \notin writers)

Liveness == ReadersEventuallyActive /\ WritersEventuallyActive /\ ReadersEventuallyStop /\ WritersEventuallyStop

====