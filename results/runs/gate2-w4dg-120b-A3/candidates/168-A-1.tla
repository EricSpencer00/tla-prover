---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Actors == 1..NumActors

Requests == [pid: Actors, kind: {"read", "write"}]
Active == Actors \cup {0}

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

TypeOK ==
  /\ readers \subseteq Actors
  /\ writers \subseteq Actors
  /\ queue \in Seq(Requests)

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

RequestRead(p) ==
  /\ \A i \in 1..Len(queue) : queue[i].pid # p
  /\ queue' = Append(queue, [pid |-> p, kind |-> "read"])
  /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
  /\ \A i \in 1..Len(queue) : queue[i].pid # p
  /\ queue' = Append(queue, [pid |-> p, kind |-> "write"])
  /\ UNCHANGED <<readers, writers>>

BeginServe ==
  /\ queue # <<>>
  /\ writers = {}
  /\ LET q == Head(queue) IN
       /\ IF q.kind = "read" THEN readers' = readers \cup {q.pid} ELSE readers' = readers
       /\ IF q.kind = "write" /\ readers = {} THEN writers' = writers \cup {q.pid} ELSE writers' = writers
       /\ queue' = Tail(queue)

Stop(p) ==
  /\ \/ p \in readers
     \/ p \in writers
  /\ readers' = readers \ {p}
  /\ writers' = writers \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in Actors : RequestRead(p)
  \/ \E p \in Actors : RequestWrite(p)
  \/ BeginServe
  \/ \E p \in Actors : Stop(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in Actors : RequestRead(p))
  /\ WF_vars(\E p \in Actors : RequestWrite(p))
  /\ WF_vars(BeginServe)
  /\ WF_vars(\E p \in Actors : Stop(p))

Safety ==
  /\ (writers # {} => readers = {})
  /\ (readers # {} => writers = {})
  /\ writers \subseteq Active
  /\ readers \subseteq Active

Liveness ==
  /\ \A p \in Actors : (p \in readers) ~> (p \notin readers)
  /\ \A p \in Actors : (p \in writers) ~> (p \notin writers)

====