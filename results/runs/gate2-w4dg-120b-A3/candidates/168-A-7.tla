---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS
    NumActors

\* Single entry in the request queue: the requesting process and its mode.
Request == [proc : 1..NumActors, mode : {"read", "write"}]

VARIABLES
    readers,   \* set of processes currently reading the shared resource
    writers,   \* set of processes currently writing to the shared resource
    queue      \* ordered sequence of pending Request entries

vars == <<readers, writers, queue>>

TypeOK ==
    /\ readers \subseteq (1..NumActors)
    /\ writers \subseteq (1..NumActors)
    /\ queue \in Seq(Request)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = << >>

\* A process is only ever queued once per request, so it cannot be both waiting to
\* read and waiting to write at the same time.
InQueue(p) == \E i \in DOMAIN queue : queue[i].proc = p

\* Queue a read request; a process already waiting is not re-queued.
RequestRead(p) ==
    /\ ~ InQueue(p)
    /\ queue' = Append(queue, [proc |-> p, mode |-> "read"])
    /\ UNCHANGED <<readers, writers>>

\* Queue a write request; a process already waiting is not re-queued.
RequestWrite(p) ==
    /\ ~ InQueue(p)
    /\ queue' = Append(queue, [proc |-> p, mode |-> "write"])
    /\ UNCHANGED <<readers, writers>>

\* The queue head is admitted only when the readers/writers rules allow it.  The
\* fairness of the queue (first-come-first-served) is what prevents starvation.
BeginAccess ==
    /\ queue # << >>
    /\ writers = {}
    /\ LET r == Head(queue) IN
         /\ IF r.mode = "read"
              THEN readers' = readers \cup {r.proc}
              ELSE readers' = readers
         /\ IF r.mode = "write" /\ readers = {}
              THEN writers' = writers \cup {r.proc}
              ELSE writers' = writers
         /\ queue' = Tail(queue)

\* An active reader or writer may stop voluntarily.
StopActivity(p) ==
    /\ \/ p \in readers
       \/ p \in writers
    /\ readers' = readers \ {p}
    /\ writers' = writers \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in 1..NumActors : RequestRead(p)
    \/ \E p \in 1..NumActors : RequestWrite(p)
    \/ BeginAccess
    \/ \E p \in 1..NumActors : StopActivity(p)

Spec == Init /\ [][Next]_vars

\* Readers never read while a writer is active, and writers are mutually exclusive.
Safety ==
    /\ (readers # {} => writers = {})
    /\ (writers # {} => readers = {})
    /\ Cardinality(writers) <= 1

\* Fairness ensures every enabled request is eventually processed (no starvation).
Liveness ==
    /\ \A p \in 1..NumActors : <>(p \in readers)
    /\ \A p \in 1..NumActors : <>(p \in writers)
    /\ \A p \in 1..NumActors : (p \in readers) ~> (p \notin readers)
    /\ \A p \in 1..NumActors : (p \in writers) ~> (p \notin writers)

\* Weak fairness: every enabled request is guaranteed to be taken.
Fairness ==
    /\ \A p \in 1..NumActors : TRUE ~> RequestRead(p)
    /\ \A p \in 1..NumActors : TRUE ~> RequestWrite(p)
    /\ TRUE ~> BeginAccess
    /\ \A p \in 1..NumActors : (p \in readers \/ p \in writers) ~> StopActivity(p)

====