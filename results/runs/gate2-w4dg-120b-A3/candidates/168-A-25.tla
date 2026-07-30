---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

Processes == {1..NumActors}

VARIABLES readers, writers, queue
vars == <<readers, writers, queue>>

Req == [kind : {"read", "write"}, who : Processes]

TypeOK ==
  /\ readers \subseteq Processes
  /\ writers \subseteq Processes
  /\ queue \in Seq(Req)

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

RequestRead(p) ==
  /\ \A i \in 1..Len(queue) : ~(queue[i].kind = "read" /\ queue[i].who = p)
  /\ queue' = Append(queue, [kind |-> "read", who |-> p])
  /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
  /\ \A i \in 1..Len(queue) : ~(queue[i].kind = "write" /\ queue[i].who = p)
  /\ queue' = Append(queue, [kind |-> "write", who |-> p])
  /\ UNCHANGED <<readers, writers>>

BeginAccess ==
  /\ Len(queue) > 0
  /\ writers = {}
  /\ LET q == Head(queue) IN
       /\ queue' = Tail(queue)
       /\ IF q.kind = "read" THEN readers' = readers \cup {q.who} /\ writers' = writers
          ELSE readers' = readers /\ writers' = writers \cup {q.who}

StopActivity(p) ==
  /\ \/ p \in readers
     \/ p \in writers
  /\ readers' = readers \ {p}
  /\ writers' = writers \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in Processes : RequestRead(p) \/ RequestWrite(p) \/ StopActivity(p)
  \/ BeginAccess

Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E p \in Processes : RequestRead(p))
  /\ WF_vars(\E p \in Processes : RequestWrite(p))
  /\ WF_vars(BeginAccess)
  /\ WF_vars(\E p \in Processes : StopActivity(p))

ReadersActive == \E p \in Processes : p \in readers
WritersActive == \E p \in Processes : p \in writers

Safety ==
  /\ ReadersActive => writers = {}
  /\ WritersActive => readers = {}
  /\ Cardinality(writers) <= 1

Liveness ==
  /\ \A p \in Processes : (p \in readers) ~> (p \notin readers)
  /\ \A p \in Processes : (p \in writers) ~> (p \notin writers)

====