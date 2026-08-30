---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* Queue: first element is the head of the request line; each request records
\* the actor and whether it wants to read or write.
VARIABLES readers, writers, queue
vars == <<readers, writers, queue>>

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = << >>

\* A process that is not already waiting joins the queue with a read request.
RequestRead(p) ==
  /\ \A i \in DOMAIN queue : queue[i].actor # p
  /\ queue' = Append(queue, [actor |-> p, mode |-> "read"])
  /\ UNCHANGED <<readers, writers>>

\* A process that is not already waiting joins the queue with a write request.
RequestWrite(p) ==
  /\ \A i \in DOMAIN queue : queue[i].actor # p
  /\ queue' = Append(queue, [actor |-> p, mode |-> "write"])
  /\ UNCHANGED <<readers, writers>>

\* The head of the queue is processed: a read joins the readers set,
\* a write joins the writers set only when no one is reading.
BeginService ==
  /\ queue # << >>
  /\ writers = {}
  /\ LET top == Head(queue) IN
       /\ IF top.mode = "read"
          THEN readers' = readers \cup {top.actor}
          ELSE IF readers = {}
               THEN writers' = writers \cup {top.actor}
               ELSE UNCHANGED writers
       /\ queue' = Tail(queue)
  /\ UNCHANGED readers

\* Any active reader or writer may voluntarily stop.
Stop(p) ==
  /\ readers' = readers \ {p}
  /\ writers' = writers \ {p}
  /\ UNCHANGED queue

Next ==
  \/ BeginService
  \/ \E p \in NumActors : RequestRead(p) \/ RequestWrite(p) \/ Stop(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(BeginService)
  /\ \A p \in NumActors : WF_vars(Stop(p))

TypeOK ==
  /\ readers \subseteq NumActors
  /\ writers \subseteq NumActors
  /\ \A i \in DOMAIN queue : queue[i].actor \in NumActors

\* Readers and writers are mutually exclusive; at most one writer is active.
Safety ==
  /\ (writers # {} => readers = {})
  /\ \A p, q \in writers : p = q

\* Every process eventually gets to read and to write.
Liveness ==
  \A p \in NumActors : (\A>><<\X>><> readers) /\ (\A>><<\X>><> writers)
====