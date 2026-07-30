---- MODULE ReadersWriters ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS NumActors

\* Queue position in the fair solution; n is a bounded override of NumActors
n == 3

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

Waiting == [type : {"read", "write"}, who : 1..NumActors]

TypeOK ==
  /\ readers \subseteq (1..NumActors)
  /\ writers \subseteq (1..NumActors)
  /\ queue \in Seq(Waiting)

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

RequestRead(p) ==
  /\ \A i \in 1..Len(queue) : queue[i].who # p
  /\ queue' = Append(queue, [type |-> "read", who |-> p])
  /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
  /\ \A i \in 1..Len(queue) : queue[i].who # p
  /\ queue' = Append(queue, [type |-> "write", who |-> p])
  /\ UNCHANGED <<readers, writers>>

BeginAccess ==
  /\ queue # <<>>
  /\ writers = {}
  /\ LET q == Head(queue) IN
       /\ IF q.type = "read" \/ readers = {}
          THEN readers' = readers \cup {q.who}
          ELSE readers' = readers
       /\ IF q.type = "write" /\ readers = {}
          THEN writers' = writers \cup {q.who}
          ELSE writers' = writers
       /\ queue' = Tail(queue)

StopActivity(p) ==
  /\ \/ readers' = readers \ {p}
     \/ writers' = writers \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in 1..NumActors : RequestRead(p)
  \/ \E p \in 1..NumActors : RequestWrite(p)
  \/ BeginAccess
  \/ \E p \in 1..NumActors : StopActivity(p)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..NumActors : RequestRead(p))
  /\ WF_vars(\E p \in 1..NumActors : RequestWrite(p))
  /\ WF_vars(BeginAccess)
  /\ WF_vars(\E p \in 1..NumActors : StopActivity(p))

Safety ==
  /\ readers \cap writers = {}
  /\ Cardinality(writers) <= 1

Liveness ==
  /\ \A p \in 1..NumActors :
       /\ (\A f \in {readers, writers} : (p \in f) ~> (p \notin f))
  /\ \A p \in 1..NumActors : (p \in readers) ~> (p \notin readers)
  /\ \A p \in 1..NumActors : (p \in writers) ~> (p \notin writers)

====