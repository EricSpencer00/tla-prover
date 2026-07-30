---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* n is the finite set of actor identities; the .cfg file substitutes it for
\* NumActors so the model stays bounded.
n == NumActors

VARIABLES readers, writers, queue

vars == << readers, writers, queue >>

Requests == [kind : {"read", "write"}, who : n]

TypeOK ==
  /\ readers \subseteq n
  /\ writers \subseteq n
  /\ queue \in Seq(Requests)

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = << >>

\* A process that is not already waiting to read joins the end of the queue.
RequestRead(p) ==
  /\ \A i \in 1..Len(queue) : queue[i].who # p
  /\ queue' = Append(queue, [kind |-> "read", who |-> p])
  /\ UNCHANGED << readers, writers >>

\* A process that is not already waiting to write joins the end of the queue.
RequestWrite(p) ==
  /\ \A i \in 1..Len(queue) : queue[i].who # p
  /\ queue' = Append(queue, [kind |-> "write", who |-> p])
  /\ UNCHANGED << readers, writers >>

\* The head of the queue is granted only when it is compatible with the
\* current activity: reads are always compatible with reads, writes need
\* exclusive access.
BeginAccess ==
  /\ queue # << >>
  /\ writers = {}
  /\ LET r == Head(queue) IN
       /\ r.kind = "read" \/ (r.kind = "write" /\ readers = {})
       /\ readers' = IF r.kind = "read" THEN readers \cup {r.who} ELSE readers
       /\ writers' = IF r.kind = "write" THEN writers \cup {r.who} ELSE writers
       /\ queue' = Tail(queue)

\* Any active reader or writer may voluntarily stop.
StopActivity(p) ==
  /\ p \in readers \/ p \in writers
  /\ readers' = readers \ {p}
  /\ writers' = writers \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in n : RequestRead(p)
  \/ \E p \in n : RequestWrite(p)
  \/ BeginAccess
  \/ \E p \in n : StopActivity(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in n : RequestRead(p))
  /\ WF_vars(\E p \in n : RequestWrite(p))
  /\ WF_vars(BeginAccess)
  /\ WF_vars(\E p \in n : StopActivity(p))

\* Readers and writers are never active at the same time.
Safety ==
  /\ (writers # {} => readers = {})
  /\ (readers # {} => writers = {})
  /\ Cardinality(writers) <= 1

\* Every process eventually gets to read and to write.
Liveness ==
  /\ \A p \in n : <>(p \in readers)
  /\ \A p \in n : <>(p \in writers)
  /\ \A p \in n : <>(p \notin readers)
  /\ \A p \in n : <>(p \notin writers)

====