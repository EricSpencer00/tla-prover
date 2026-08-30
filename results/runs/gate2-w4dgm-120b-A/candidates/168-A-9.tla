---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* Three state variables: who is reading, who is writing, and the pending queue.
VARIABLES readers, writers, queue

Actors == 1..NumActors

TypeOK ==
  /\ readers \subseteq Actors
  /\ writers \subseteq Actors
  /\ queue \in Seq([mode: {"read", "write"}, pid: Actors])

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

\* A process joins the waiting queue for a read, if it is not already queued.
RequestRead(p) ==
  /\ \A i \in DOMAIN queue : queue[i].pid # p
  /\ queue' = Append(queue, [mode |-> "read", pid |-> p])
  /\ UNCHANGED <<readers, writers>>

\* A process joins the waiting queue for a write, if it is not already queued.
RequestWrite(p) ==
  /\ \A i \in DOMAIN queue : queue[i].pid # p
  /\ queue' = Append(queue, [mode |-> "write", pid |-> p])
  /\ UNCHANGED <<readers, writers>>

\* The queue is processed in order; a write is only granted when no one is reading.
BeginAccess ==
  /\ queue # <<>>
  /\ writers = {}
  /\ LET head == queue[1] IN
       /\ IF head.mode = "read" THEN readers' = readers \cup {head.pid} ELSE readers' = readers
       /\ IF head.mode = "write" /\ readers = {} THEN writers' = writers \cup {head.pid} ELSE writers' = writers
       /\ queue' = Tail(queue)

\* Any active participant may voluntarily stop its activity.
StopActivity(p) ==
  \/ readers' = readers \ {p}
  \/ writers' = writers \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in Actors: RequestRead(p)
  \/ \E p \in Actors: RequestWrite(p)
  \/ BeginAccess
  \/ \E p \in Actors: StopActivity(p)

\* Fairness of every individual action guarantees no request is postponed forever.
Spec ==
  /\ Init
  /\ [][Next]_<<readers, writers, queue>>
  /\ \A p \in Actors: WF_vars(RequestRead(p)) /\ WF_vars(RequestWrite(p))
  /\ WF_vars(BeginAccess)
  /\ \A p \in Actors: WF_vars(StopActivity(p))

\* Safety: readers and writers are never active at the same time, and writers are exclusive.
Safety ==
  /\ (writers # {} => readers = {})
  /\ writers \subseteq (Actors \ readers)

\* Every actor eventually gets to read and eventually gets to write.
Liveness ==
  \A p \in Actors: (p \in readers) ~> (p \in readers) /\ (p \in writers) ~> (p \in writers)

\* The .cfg substitutes the concrete bound n for the abstract constant NumActors.
n == 2

====