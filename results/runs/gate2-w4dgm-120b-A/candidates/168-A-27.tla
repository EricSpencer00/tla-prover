---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

ASSUME /\ NumActors \in Nat
       /\ NumActors >= 1
       /\ Cardinality(NumActors) = Cardinality(NumActors)

ACTORS == 1..NumActors

TypeOK ==
  /\ readers \subseteq ACTORS
  /\ writers \subseteq ACTORS
  /\ queue \in Seq([actor: ACTORS, kind: {"read", "write"}])

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = << >>

RequestRead(a) ==
  /\ ~\E i \in 1..Len(queue) : queue[i].actor = a /\ queue[i].kind = "read"
  /\ queue' = Append(queue, [actor |-> a, kind |-> "read"])
  /\ readers' = readers
  /\ writers' = writers

RequestWrite(a) ==
  /\ ~\E i \in 1..Len(queue) : queue[i].actor = a /\ queue[i].kind = "write"
  /\ queue' = Append(queue, [actor |-> a, kind |-> "write"])
  /\ readers' = readers
  /\ writers' = writers

ProcessRequest ==
  /\ queue # << >>
  /\ writers = {}
  /\ LET head == Head(queue) IN
       /\ \/ /\ head.kind = "read"
             /\ readers' = readers \cup {head.actor}
             /\ writers' = writers
          \/ /\ head.kind = "write"
             /\ readers = {}
             /\ readers' = {}
             /\ writers' = writers \cup {head.actor}
       /\ queue' = Tail(queue)

StopActivity(a) ==
  /\ \/ readers' = readers \ {a}
       \/ writers' = writers \ {a}
  /\ queue' = queue
  /\ readers' \in SUBSET readers
  /\ writers' \in SUBSET writers

Next ==
  \/ \E a \in ACTORS : RequestRead(a)
  \/ \E a \in ACTORS : RequestWrite(a)
  \/ ProcessRequest
  \/ \E a \in ACTORS : StopActivity(a)

Spec ==
  /\ Init
  /\ [][Next]_<<readers, writers, queue>>
  /\ \A a \in ACTORS : SF_vars(RequestRead(a))
  /\ \A a \in ACTORS : SF_vars(RequestWrite(a))
  /\ SF_vars(ProcessRequest)
  /\ \A a \in ACTORS : SF_vars(StopActivity(a))

Safety ==
  /\ ~(readers = {} /\ writers # {})
  /\ \A w1, w2 \in writers : w1 = w2

Liveness ==
  /\ \A a \in ACTORS :
       /\ (a \in readers) ~> (a \notin readers)
       /\ (a \in writers) ~> (a \notin writers)

====