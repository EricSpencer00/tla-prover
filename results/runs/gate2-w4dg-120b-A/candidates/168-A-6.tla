---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Processes == 1 .. NumActors
RequestKinds == {"read", "write"}

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

TypeOK ==
  /\ readers \subseteq Processes
  /\ writers \subseteq Processes
  /\ queue \in Seq([kind: RequestKinds, who: Processes])

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

RequestToRead(p) ==
  /\ \A i \in DOMAIN queue : queue[i].who # p
  /\ queue' = Append(queue, [kind |-> "read", who |-> p])
  /\ UNCHANGED <<readers, writers>>

RequestToWrite(p) ==
  /\ \A i \in DOMAIN queue : queue[i].who # p
  /\ queue' = Append(queue, [kind |-> "write", who |-> p])
  /\ UNCHANGED <<readers, writers>>

BeginIO ==
  /\ queue # <<>>
  /\ writers = {}
  /\ LET front == Head(queue) IN
       IF front.kind = "read" THEN
         /\ readers' = readers \cup {front.who}
         /\ writers' = writers
       ELSE
         /\ writers' = IF readers = {} THEN writers \cup {front.who} ELSE writers
         /\ readers' = readers
  /\ queue' = Tail(queue)

StopActivity(p) ==
  /\ \/ p \in readers
       \/ p \in writers
  /\ readers' = readers \ {p}
  /\ writers' = writers \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in Processes : RequestToRead(p)
  \/ \E p \in Processes : RequestToWrite(p)
  \/ BeginIO
  \/ \E p \in Processes : StopActivity(p)

Spec == Init /\ [][Next]_vars

\* Readers and writers never act at the same time; at most one writer at once.
Safety == readers # {} => writers = {} /\ Cardinality(writers) <= 1

Liveness ==
  /\ \A p \in Processes : <>(p \in readers)
  /\ \A p \in Processes : <>(p \in writers)
  /\ \A p \in Processes : (p \in readers) ~> (p \notin readers)
  /\ \A p \in Processes : (p \in writers) ~> (p \notin writers)

====