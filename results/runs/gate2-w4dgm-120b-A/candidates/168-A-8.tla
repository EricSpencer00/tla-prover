---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

\* Safety requires readers and writers to be mutually exclusive and only one
\* writer active at a time. Liveness requires every actor to eventually read
\* and eventually write, which the queue ordering plus weak fairness ensures.

VARIABLES activeReaders, activeWriters, queue

TypeOK ==
  /\ activeReaders \subseteq NumActors
  /\ activeWriters \subseteq NumActors
  /\ queue \in Seq([mode: {"read", "write"}, actor: NumActors])

Init ==
  /\ activeReaders = {}
  /\ activeWriters = {}
  /\ queue = <<>>

RequestRead(a) ==
  /\ ~ \E i \in 1..Len(queue): queue[i].actor = a /\ queue[i].mode = "read"
  /\ queue' = Append(queue, [mode |-> "read", actor |-> a])
  /\ UNCHANGED <<activeReaders, activeWriters>>

RequestWrite(a) ==
  /\ ~ \E i \in 1..Len(queue): queue[i].actor = a /\ queue[i].mode = "write"
  /\ queue' = Append(queue, [mode |-> "write", actor |-> a])
  /\ UNCHANGED <<activeReaders, activeWriters>>

BeginService ==
  /\ Len(queue) > 0
  /\ activeWriters = {}
  /\ LET front == Head(queue) IN
       /\ queue' = Tail(queue)
       /\ IF front.mode = "read"
            THEN activeReaders' = activeReaders \cup {front.actor}
            ELSE IF activeReaders = {}
                 THEN activeWriters' = activeWriters \cup {front.actor}
                 ELSE activeWriters' = activeWriters \cup {front.actor}
       \/ UNCHANGED <<activeWriters, activeReaders>>

StopActivity(a) ==
  \/ /\ a \in activeReaders
     /\ activeReaders' = activeReaders \ {a}
     /\ UNCHANGED <<activeWriters, queue>>
  \/ /\ a \in activeWriters
     /\ activeWriters' = activeWriters \ {a}
     /\ UNCHANGED <<activeReaders, queue>>

Next ==
  \/ \E a \in NumActors: RequestRead(a)
  \/ \E a \in NumActors: RequestWrite(a)
  \/ BeginService
  \/ \E a \in NumActors: StopActivity(a)

Spec ==
  /\ Init
  /\ [][Next]_<<activeReaders, activeWriters, queue>>
  /\ WF_Vars(\E a \in NumActors: RequestRead(a))
  /\ WF_Vars(\E a \in NumActors: RequestWrite(a))
  /\ WF_Vars(BeginService)
  /\ \A a \in NumActors: WF_Vars(StopActivity(a))

Safety ==
  /\ (activeReaders # {}) => (activeWriters = {})
  /\ (activeWriters # {}) => (activeReaders = {})
  /\ Cardinality(activeWriters) <= 1

Liveness ==
  /\ \A a \in NumActors: (a \in activeReaders) ~> (a \notin activeReaders)
  /\ \A a \in NumActors: (a \in activeWriters) ~> (a \notin activeWriters)

====