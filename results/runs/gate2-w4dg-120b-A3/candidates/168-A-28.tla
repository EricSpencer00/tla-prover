---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS
  NumActors

ASSUME NumActors \in Nat /\ NumActors > 0

\* The bounded version of NumActors used in the .cfg overrides this
\* operator via substitution: n == NumActors.
n == NumActors

Actors == 1..NumActors

VARIABLES
  readers,
  writers,
  queue

vars == <<readers, writers, queue>>

Req == [actor : Actors, rw : {"read", "write"}]

TypeOK ==
  /\ readers \subseteq Actors
  /\ writers \subseteq Actors
  /\ queue \in Seq(Req)

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

\* A process that is not already waiting to read joins the waiting queue.
RequestRead(a) ==
  /\ \A i \in 1..Len(queue) : queue[i].actor # a
  /\ queue' = Append(queue, [actor |-> a, rw |-> "read"])
  /\ UNCHANGED <<readers, writers>>

\* A process that is not already waiting to write joins the waiting queue.
RequestWrite(a) ==
  /\ \A i \in 1..Len(queue) : queue[i].actor # a
  /\ queue' = Append(queue, [actor |-> a, rw |-> "write"])
  /\ UNCHANGED <<readers, writers>>

\* The head request is serviced in a first-come-first-served order: a read
\* is granted when no writer is active; a write is granted only when no
\* reader is active. Either way the request leaves the head of the queue.
BeginService ==
  /\ queue # <<>>
  /\ writers = {}
  /\ LET req == Head(queue) IN
       IF req.rw = "read" THEN
         /\ readers' = readers \cup {req.actor}
         /\ writers' = writers
       ELSE
         /\ readers = {}
         /\ readers' = readers
         /\ writers' = writers \cup {req.actor}
     /\ queue' = Tail(queue)

\* Any active reader or writer may voluntarily stop.
StopActivity ==
  /\ \E a \in readers \cup writers :
       readers' = readers \ {a}
       /\ writers' = writers \ {a}
  /\ UNCHANGED queue

Next ==
  \/ BeginService
  \/ StopActivity
  \/ \E a \in Actors :
       RequestRead(a) \/ RequestWrite(a)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(RequestRead(1))
  /\ WF_vars(RequestWrite(1))
  /\ WF_vars(BeginService)
  /\ WF_vars(StopActivity)

\* Readers and writers are never simultaneously active.
Safety ==
  /\ readers # {}
     => writers = {}
  /\ writers # {}
     => readers = {}

\* No process is starved: every process eventually gets to read, and
\* every process eventually gets to write, even though it may be slow.
Liveness ==
  /\ \A a \in Actors : <>(a \in readers)
  /\ \A a \in Actors : <>(a \in writers)
  /\ \A a \in Actors : <>(a \notin readers)
  /\ \A a \in Actors : <>(a \notin writers)

====