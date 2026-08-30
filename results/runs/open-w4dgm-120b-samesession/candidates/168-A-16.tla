---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

ASSUME NumActors \in Nat /\ NumActors >= 1

Actors == 0 .. (NumActors - 1)

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

TypeOK ==
  /\ readers \subseteq Actors
  /\ writers \subseteq Actors
  /\ queue \in Seq([pid : Actors, mode : {"read", "write"}])

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

IsWaiting(p) ==
  \E i \in 1 .. Len(queue) : queue[i].pid = p

\* A process that is not already queued asks to read; it joins the tail of the queue.
RequestRead(p) ==
  /\ ~IsWaiting(p)
  /\ queue' = Append(queue, [pid |-> p, mode |-> "read"])
  /\ UNCHANGED <<readers, writers>>

\* A process that is not already queued asks to write; it joins the tail of the queue.
RequestWrite(p) ==
  /\ ~IsWaiting(p)
  /\ queue' = Append(queue, [pid |-> p, mode |-> "write"])
  /\ UNCHANGED <<readers, writers>>

\* The head of the queue is serviced only when it does not conflict with an active writer
\* (for a read) or with any active reader (for a write), providing mutual exclusion.
BeginAccess ==
  /\ queue # <<>>
  /\ writers = {}
  /\ LET front == Head(queue) IN
       \/ front.mode = "read"
          /\ readers' = readers \cup {front.pid}
          /\ writers' = writers
          /\ queue' = Tail(queue)
       \/ front.mode = "write"
          /\ readers = {}
          /\ writers' = writers \cup {front.pid}
          /\ readers' = readers
          /\ queue' = Tail(queue)

\* An active reader or writer voluntarily stops.
StopActivity(p) ==
  /\ (p \in readers \/ p \in writers)
  /\ readers' = readers \ {p}
  /\ writers' = writers \ {p}
  /\ UNCHANGED <<queue>>

Next ==
  \/ BeginAccess
  \/ \E p \in Actors : RequestRead(p) \/ RequestWrite(p) \/ StopActivity(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Actors : SF_vars(RequestRead(p))
  /\ \A p \in Actors : SF_vars(RequestWrite(p))
  /\ SF_vars(BeginAccess)
  /\ \A p \in Actors : SF_vars(StopActivity(p))

\* Safety: readers and writers are mutually exclusive, and writers are at most one.
Safety ==
  /\ readers \cap writers = {}
  /\ \A a, b \in writers : a = b

\* Liveness: every process eventually gets to read and eventually gets to write.
Liveness ==
  /\ \A p \in Actors : (p \notin readers) ~> (p \in readers)
  /\ \A p \in Actors : (p \notin writers) ~> (p \in writers)

\* The .cfg file substitutes a finite bound for n; here n is the same as NumActors.
n == NumActors
====