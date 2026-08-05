---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Actors == 0 .. (NumActors - 1)
NONE == 99
Kinds == {"read", "write"}

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

Requests == [k : Kinds, a : Actors]

TypeOK ==
  /\ readers \subseteq Actors
  /\ writers \subseteq Actors
  /\ queue \in Seq(Requests)

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

RequestRead(a) ==
  /\ \A i \in 1 .. Len(queue) : queue[i].a # a \/ queue[i].k # "read"
  /\ queue' = Append(queue, [k |-> "read", a |-> a])
  /\ UNCHANGED <<readers, writers>>

RequestWrite(a) ==
  /\ \A i \in 1 .. Len(queue) : queue[i].a # a \/ queue[i].k # "write"
  /\ queue' = Append(queue, [k |-> "write", a |-> a])
  /\ UNCHANGED <<readers, writers>>

ProcessQueue ==
  /\ Len(queue) > 0
  /\ writers = {}
  /\ LET h == Head(queue) IN
       /\ IF h.k = "read" THEN readers' = readers \cup {h.a} ELSE readers' = readers
       /\ IF h.k = "write" /\ readers = {} THEN writers' = writers \cup {h.a} ELSE writers' = writers
  /\ queue' = Tail(queue)

StopActive(a) ==
  /\ (a \in readers \/ a \in writers)
  /\ readers' = readers \ {a}
  /\ writers' = writers \ {a}
  /\ UNCHANGED queue

Next ==
  \/ \E a \in Actors : RequestRead(a)
  \/ \E a \in Actors : RequestWrite(a)
  \/ ProcessQueue
  \/ \E a \in Actors : StopActive(a)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E a \in Actors : RequestRead(a))
  /\ WF_vars(\E a \in Actors : RequestWrite(a))
  /\ WF_vars(ProcessQueue)
  /\ WF_vars(\E a \in Actors : StopActive(a))

\* No simultaneous readers and writers: whenever a write is active, no read is, and
\* the writer set is always of size at most one.
Safety ==
  /\ (writers # {} => readers = {})
  /\ (writers = {} \/ writers = {CHOOSE w \in writers : TRUE})

\* Every actor eventually gets to read and eventually gets to write -- strong
\* fairness here, layered on top of the weak fairness already in Spec.
Liveness ==
  /\ \A a \in Actors : <>(a \in readers)
  /\ \A a \in Actors : <>(a \in writers)
  /\ \A a \in Actors : <>(a \notin readers)
  /\ \A a \in Actors : <>(a \notin writers)

====