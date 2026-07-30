---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

VARIABLES readers, writers, queue
vars == <<readers, writers, queue>>

Reqs == {"read", "write"}
Acts == 1..NumActors

TypeOK ==
  /\ readers \subseteq Acts
  /\ writers \subseteq Acts
  /\ queue \in Seq([act : Reqs, who : Acts])

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

RequestRead(a) ==
  /\ ~ \E k \in 1..Len(queue) : queue[k].who = a /\ queue[k].act = "read"
  /\ queue' = Append(queue, [act |-> "read", who |-> a])
  /\ UNCHANGED <<readers, writers>>

RequestWrite(a) ==
  /\ ~ \E k \in 1..Len(queue) : queue[k].who = a /\ queue[k].act = "write"
  /\ queue' = Append(queue, [act |-> "write", who |-> a])
  /\ UNCHANGED <<readers, writers>>

Begin ==
  /\ queue # <<>>
  /\ writers = {}
  /\ LET req == Head(queue) IN
       /\ IF req.act = "read" THEN readers' = readers \cup {req.who}
          ELSE /\ readers = {}
               /\ writers' = writers \cup {req.who}
       /\ queue' = Tail(queue)

Stop ==
  /\ \E a \in readers : readers' = readers \ {a} /\ UNCHANGED writers
  /\ \E a \in writers : writers' = writers \ {a} /\ UNCHANGED readers
  /\ UNCHANGED queue

Next ==
  \/ \E a \in Acts : RequestRead(a)
  \/ \E a \in Acts : RequestWrite(a)
  \/ Begin
  \/ Stop

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E a \in Acts : RequestRead(a))
  /\ WF_vars(\E a \in Acts : RequestWrite(a))
  /\ WF_vars(Begin)
  /\ WF_vars(Stop)

Safety ==
  /\ (writers = {} \/ readers = {})
  /\ Cardinality(writers) <= 1

Liveness ==
  /\ \A a \in Acts : (a \in readers) ~> (a \notin readers)
  /\ \A a \in Acts : (a \in writers) ~> (a \notin writers)

n == NumActors
====