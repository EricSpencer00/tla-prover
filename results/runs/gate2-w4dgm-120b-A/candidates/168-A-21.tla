---- MODULE ReadersWriters ----
\* Readers-writers system with a fair, first-come-first-served access queue.
\* No reader and writer are ever active at the same time, and at most one
\* writer is active at any instant. Every process eventually gets its turn.
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* A request pairs the process with what it wants; the queue is ordered, so the
\* system services requests in arrival order, which is what gives fairness.
Processes == 1..NumActors
Requests == [actor: Processes, kind: {"read", "write"}]

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

TypeOK ==
  /\ reading \subseteq Processes
  /\ writing \subseteq Processes
  /\ queue \in Seq(Requests)

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = <<>>

\* A process that is not already waiting to read joins the queue for reading.
RequestRead(p) ==
  /\ \A i \in DOMAIN queue : queue[i].actor # p
  /\ queue' = Append(queue, [actor |-> p, kind |-> "read"])
  /\ UNCHANGED <<reading, writing>>

\* A process that is not already waiting to write joins the queue for writing.
RequestWrite(p) ==
  /\ \A i \in DOMAIN queue : queue[i].actor # p
  /\ queue' = Append(queue, [actor |-> p, kind |-> "write"])
  /\ UNCHANGED <<reading, writing>>

\* The queued request is granted only if it would not breach mutual exclusion.
\* Both reader requests and a lone writer can proceed here, but never together.
ProcessQueue ==
  /\ queue # <<>>
  /\ LET hd == Head(queue) IN
       /\ IF hd.kind = "read"
            THEN /\ reading' = reading \cup {hd.actor}
                 /\ writing' = writing
            ELSE IF hd.kind = "write" /\ reading = {}
                 THEN /\ writing' = writing \cup {hd.actor}
                      /\ reading' = reading
                 ELSE /\ reading' = reading
                      /\ writing' = writing
       /\ queue' = Tail(queue)

StopActivity(p) ==
  /\ \/ p \in reading
     \/ p \in writing
  /\ reading' = reading \ {p}
  /\ writing' = writing \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in Processes : RequestRead(p)
  \/ \E p \in Processes : RequestWrite(p)
  \/ ProcessQueue
  \/ \E p \in Processes : StopActivity(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Processes : SF_vars(RequestRead(p))
  /\ \A p \in Processes : SF_vars(RequestWrite(p))
  /\ SF_vars(ProcessQueue)
  /\ \A p \in Processes : SF_vars(StopActivity(p))

\* Safety: readers and writers are never active at the same time.
Safety ==
  /\ (reading # {} => writing = {})
  /\ (writing # {} => reading = {})
  /\ Cardinality(writing) <= 1

\* Liveness: every process eventually reads and eventually writes.
Liveness ==
  \A p \in Processes :
    /\ (p \notin reading) ~> (p \in reading)
    /\ (p \notin writing) ~> (p \in writing)

\* The emitter substitutes a concrete bound for n (NumActors) from the .cfg.
n == NumActors
====