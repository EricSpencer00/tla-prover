---- MODULE ReadersWriters ----
EXTENDS Integers, Sequences

CONSTANTS NumActors

Actors == 1..NumActors
Modes == {"read", "write"}

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

InQueue(a) == \E i \in 1..Len(queue) : queue[i].actor = a

TypeOK ==
  /\ readers \subseteq Actors
  /\ writers \subseteq Actors
  /\ queue \in Seq([actor : Actors, mode : Modes])

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = << >>

RequestRead(a) ==
  /\ ~InQueue(a)
  /\ queue' = Append(queue, [actor |-> a, mode |-> "read"])
  /\ UNCHANGED <<readers, writers>>

RequestWrite(a) ==
  /\ ~InQueue(a)
  /\ queue' = Append(queue, [actor |-> a, mode |-> "write"])
  /\ UNCHANGED <<readers, writers>>

BeginAccess ==
  /\ Len(queue) > 0
  /\ writers = {}
  /\ LET head == Head(queue) IN
       /\ IF head.mode = "read" THEN
            readers' = readers \cup {head.actor}
          ELSE
            /\ readers = {}
            /\ writers' = writers \cup {head.actor}
       /\ queue' = Tail(queue)
  /\ UNCHANGED <<readers, writers>>

StopRead(a) ==
  /\ a \in readers
  /\ readers' = readers \ {a}
  /\ UNCHANGED <<writers, queue>>

StopWrite(a) ==
  /\ a \in writers
  /\ writers' = writers \ {a}
  /\ UNCHANGED <<readers, queue>>

Next ==
  \/ \E a \in Actors : RequestRead(a)
  \/ \E a \in Actors : RequestWrite(a)
  \/ \E a \in Actors : StopRead(a)
  \/ \E a \in Actors : StopWrite(a)
  \/ BeginAccess

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E a \in Actors : RequestRead(a))
  /\ WF_vars(\E a \in Actors : RequestWrite(a))
  /\ WF_vars(BeginAccess)
  /\ \A a \in Actors : WF_vars(StopRead(a))
  /\ \A a \in Actors : WF_vars(StopWrite(a))

Safety ==
  /\ readers \cap writers = {}
  /\ Cardinality(writers) <= 1

Liveness ==
  /\ \A a \in Actors : (a \in readers) ~> (a \notin readers)
  /\ \A a \in Actors : (a \in writers) ~> (a \notin writers)

====