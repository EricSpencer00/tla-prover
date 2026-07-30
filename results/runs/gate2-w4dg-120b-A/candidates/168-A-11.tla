---- MODULE ReadersWriters ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS NumActors

Processes == 1 .. NumActors
Kinds == {"read", "write"}

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

Requests == [kind : Kinds, proc : Processes]

TypeOK ==
  /\ readers \subseteq Processes
  /\ writers \subseteq Processes
  /\ queue \in Seq(Requests)

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

RequestRead(p) ==
  /\ \A i \in DOMAIN queue : queue[i].proc # p
  /\ queue' = Append(queue, [kind |-> "read", proc |-> p])
  /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
  /\ \A i \in DOMAIN queue : queue[i].proc # p
  /\ queue' = Append(queue, [kind |-> "write", proc |-> p])
  /\ UNCHANGED <<readers, writers>>

BeginAccess ==
  /\ queue # <<>>
  /\ writers = {}
  /\ LET rq == Head(queue) IN
       /\ IF rq.kind = "read"
            THEN readers' = readers \cup {rq.proc}
            ELSE readers' = readers
       /\ IF rq.kind = "write" /\ readers = {}
            THEN writers' = writers \cup {rq.proc}
            ELSE writers' = writers
       /\ queue' = Tail(queue)

Stop(p) ==
  /\ \/ p \in readers
     \/ p \in writers
  /\ readers' = readers \ {p}
  /\ writers' = writers \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in Processes : RequestRead(p)
  \/ \E p \in Processes : RequestWrite(p)
  \/ BeginAccess
  \/ \E p \in Processes : Stop(p)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E p \in Processes : RequestRead(p))
  /\ WF_vars(\E p \in Processes : RequestWrite(p))
  /\ WF_vars(BeginAccess)
  /\ WF_vars(\E p \in Processes : Stop(p))

Safety ==
  /\ (writers # {} => readers = {})
  /\ (readers # {} => writers = {})
  /\ Cardinality(writers) <= 1

Liveness ==
  /\ \A p \in Processes : (p \notin readers) ~> (p \in readers)
  /\ \A p \in Processes : (p \notin writers) ~> (p \in writers)
  /\ \A p \in Processes : (p \in readers) ~> (p \notin readers)
  /\ \A p \in Processes : (p \in writers) ~> (p \notin writers)

====