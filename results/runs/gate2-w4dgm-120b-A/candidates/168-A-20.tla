---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

ASSUME /\ NumActors \in Nat /\ NumActors >= 1
       /\ \E n \in Nat : n = NumActors

Nodes == 1..NumActors

\* request p = "r" is a read request, request p = "w" is a write request
\* The queue is an ordered log of requests, consumed from the front.
\* The fairness conditions on RequestR/W and ProcessQueue below are what
\* give every queued request its turn, a literal fairness of access.

VARIABLES readers, writers, queue
vars == <<readers, writers, queue>>

TypeOK ==
  /\ readers \subseteq Nodes
  /\ writers \subseteq Nodes
  /\ queue \in Seq([proc: Nodes, req: {"r", "w"}])

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

\* A process may only enqueue a request if it is not already queued, so a
\* single process never occupies two queue slots at once.
Enqueue(p, t) == IF \E i \in 1..Len(queue) : queue[i].proc = p /\ queue[i].req = t
                 THEN queue
                 ELSE Append(queue, [proc |-> p, req |-> t])

RequestRead(p) ==
  /\ queue' = Enqueue(p, "r")
  /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
  /\ queue' = Enqueue(p, "w")
  /\ UNCHANGED <<readers, writers>>

ProcessQueue ==
  /\ queue # <<>>
  /\ writers = {}
  /\ LET h == Head(queue) IN
       \/ IF h.req = "r" THEN readers' = readers \cup {h.proc} ELSE readers' = readers
       \/ IF h.req = "w" THEN writers' = writers \cup {h.proc} ELSE writers' = writers
       \/ queue' = Tail(queue)
  /\ UNCHANGED readers

StopActivity(p) ==
  \/ /\ p \in readers
     /\ readers' = readers \ {p}
     /\ writers' = writers
  \/ /\ p \in writers
     /\ writers' = writers \ {p}
     /\ readers' = readers
  /\ UNCHANGED queue

Next ==
  \/ \E p \in Nodes : RequestRead(p)
  \/ \E p \in Nodes : RequestWrite(p)
  \/ ProcessQueue
  \/ \E p \in Nodes : StopActivity(p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(ProcessQueue)
        /\ \A p \in Nodes : WF_vars(RequestRead(p)) /\ WF_vars(RequestWrite(p)) /\ WF_vars(StopActivity(p))

\* SAFETY: readers and writers are mutually exclusive, and writers are
\* mutually exclusive with each other (the shared resource is singly owned).
Safety ==
  /\ (readers # {} => writers = {})
  /\ (writers # {} => readers = {})
  /\ Cardinality(writers) <= 1

\* LIVENESS: every process eventually gets to read and to write, so no
\* process is starved by the fair queue service.
Liveness ==
  /\ \A p \in Nodes : (p \notin readers) ~> (p \in readers)
  /\ \A p \in Nodes : (p \notin writers) ~> (p \in writers)
  /\ \A p \in Nodes : (p \in readers) ~> (p \notin readers)
  /\ \A p \in Nodes : (p \in writers) ~> (p \notin writers)

====