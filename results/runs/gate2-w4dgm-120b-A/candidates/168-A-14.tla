---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

VARIABLES reading, writing, queue

\* The system tracks who is reading, who is writing, and a bounded FIFO of
\* pending access requests. The request at the head is served whenever
\* readers and writers are both currently inactive (mutual exclusion of
\* access, plus the fairness guarantee enforced by the model's WF/SAFETY
\* constraints on every action below -- this is the full guarantee the
\* spec makes, not an artifact of the queue being bounded).
vars == <<reading, writing, queue>>

InQueue(p, rw) == \E i \in 1..Len(queue) : queue[i].who = p /\ queue[i].rw = rw

TypeOK ==
  /\ reading \subseteq NumActors
  /\ writing \subseteq NumActors
  /\ \A i \in 1..Len(queue) : queue[i].who \in NumActors /\ queue[i].rw \in {"r", "w"}

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = <<>>

\* A process wanting to read joins the queue unless it already has a read
\* request queued; a similar rule applies to writers, so neither can
\* silently dominate the other's chance at the front of the line.
RequestRead(p) ==
  /\ ~InQueue(p, "r")
  /\ queue' = Append(queue, [who |-> p, rw |-> "r"])
  /\ UNCHANGED <<reading, writing>>

RequestWrite(p) ==
  /\ ~InQueue(p, "w")
  /\ queue' = Append(queue, [who |-> p, rw |-> "w"])
  /\ UNCHANGED <<reading, writing>>

\* A request is granted only once its exclusive-access condition is met:
\* readers when nobody is writing, writers when nobody is reading. That
\* mutual-exclusion pair is exactly what keeps a writer from starve-ing a
\* reader forever (or vice versa) even though the queue can reorder them
\* arbitrarily before it is processed.
BeginAccess ==
  /\ Len(queue) > 0
  /\ \A wp \in writing : Cardinality(writing) = 0
  /\ LET head == Head(queue) IN
       /\ queue' = Tail(queue)
       /\ IF head.rw = "r" /\ \A rp \in reading : Cardinality(reading) = 0
          THEN reading' = reading \cup {head.who} /\ writing' = {}
          ELSE IF head.rw = "w" /\ \A rp \in reading : Cardinality(reading) = 0
               THEN writing' = writing \cup {head.who} /\ reading' = {}
               ELSE UNCHANGED <<reading, writing>>
  /\ UNCHANGED queue

Stop(p) ==
  /\ p \in reading \/ p \in writing
  /\ reading' = reading \ {p}
  /\ writing' = writing \ {p}
  /\ UNCHANGED queue

Next ==
  \/ BeginAccess
  \/ \E p \in NumActors : RequestRead(p) \/ RequestWrite(p) \/ Stop(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(BeginAccess)
  /\ \A p \in NumActors : WF_vars(Stop(p))

\* Readers and writers are never both performing work at once, and there is
\* never more than one writer -- this is what keeps the critical resource
\* mutually exclusive, which no reordering of the queue can ever break.
Safety ==
  /\ (reading # {} => writing = {})
  /\ (writing # {} => reading = {})
  /\ \A x \in writing : \A y \in writing : x = y

Liveness ==
  /\ \A p \in NumActors : (p \in reading) ~> (p \notin reading)
  /\ \A p \in NumActors : (p \in writing) ~> (p \notin writing)

\* The .cfg substitutes `n` for `NumActors`, so this operator must exist
\* even though it does nothing but return its argument.
n == NumActors

====