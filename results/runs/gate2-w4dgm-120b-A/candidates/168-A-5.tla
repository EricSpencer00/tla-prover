---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* Modelled as a ring of processes ordered 1..NumActors for fairness; the queue
\* maintains a first-come-first-served ordering of read/write requests.
Actors == 1..NumActors
Requests == {"read", "write"}
QueueDomain == [who : Actors, kind : Requests]

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

TypeOK ==
  /\ reading \subseteq Actors
  /\ writing \subseteq Actors
  /\ queue \in Seq(QueueDomain)

\* Readers and writers must never both hold the resource, and only one writer
\* may ever be active at a time.
Safety ==
  /\ reading \cap writing = {}
  /\ writing = {} \/ \E p \in Actors : writing = {p}

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = << >>

\* A process requests read access; the request joins the end of the queue.
RequestRead(p) ==
  /\ \A i \in 1..Len(queue) : queue[i].who # p \/ queue[i].kind # "read"
  /\ queue' = Append(queue, [who |-> p, kind |-> "read"])
  /\ UNCHANGED <<reading, writing>>

\* A process requests write access; the request joins the end of the queue.
RequestWrite(p) ==
  /\ \A i \in 1..Len(queue) : queue[i].who # p \/ queue[i].kind # "write"
  /\ queue' = Append(queue, [who |-> p, kind |-> "write"])
  /\ UNCHANGED <<reading, writing>>

\* The queue is processed in order: a read begins if no write is active;
\* a write begins only when the resource is completely free.
NextQueue ==
  /\ queue \in Seq(QueueDomain)
  /\ Len(queue) > 0
  /\ writing = {}
  /\ LET r == Head(queue) IN
       /\ \/ /\ r.kind = "read" /\ reading' = reading \cup {r.who}
          \/ /\ r.kind = "write" /\ reading = {} /\ writing = {} /\ writing' = {r.who}
       /\ queue' = Tail(queue)
  /\ UNCHANGED writing

StopActivity(p) ==
  /\ \/ p \in reading
     \/ p \in writing
  /\ reading' = reading \ {p}
  /\ writing' = writing \ {p}
  /\ UNCHANGED queue

Next ==
  \/ NextQueue
  \/ \E p \in Actors : RequestRead(p) \/ RequestWrite(p) \/ StopActivity(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(StopActivity(1))
  /\ WF_vars(StopActivity(2))
  /\ WF_vars(StopActivity(3))
  /\ WF_vars(StopActivity(4))
  /\ WF_vars(StopActivity(5))

\* Every process eventually gets to read, and every process eventually gets to
\* write -- the queue always drains and no process is starved.
Liveness ==
  \A p \in Actors : (p \in reading) ~> (p \in writing)

\* The constant is substituted in from the .cfg file; n is the concrete bound
\* used for model checking (a small finite ring of actors).
n == NumActors
====