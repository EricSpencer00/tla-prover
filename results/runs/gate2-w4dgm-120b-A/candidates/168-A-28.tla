---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

ASSUME /\ NumActors \in Nat /\ NumActors >= 1
       /\ \E n \in Nat : n = NumActors

VARIABLES reading, writing, queue

\* reading: set of processes holding a shared read lock on the resource
\* writing: set of processes holding the exclusive write lock (at most one)
\* queue: pending access requests, each a <<kind, actor>> pair, applied FIFO
vars == <<reading, writing, queue>>

Actors == 0 .. (NumActors - 1)

TypeOK ==
  /\ reading \subseteq Actors
  /\ writing \subseteq Actors
  /\ queue \in Seq([kind: {"read", "write"}, pid: Actors])

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = <<>>

\* A process that is not already waiting to read joins the queue with a read req
RequestRead(p) ==
  /\ \A i \in DOMAIN queue : queue[i].pid # p
  /\ queue' = Append(queue, [kind |-> "read", pid |-> p])
  /\ UNCHANGED <<reading, writing>>

\* A process that is not already waiting to write joins the queue with a write req
RequestWrite(p) ==
  /\ \A i \in DOMAIN queue : queue[i].pid # p
  /\ queue' = Append(queue, [kind |-> "write", pid |-> p])
  /\ UNCHANGED <<reading, writing>>

\* The lock manager applies the head of the queue, if the lock is free in the
\* appropriate sense; a read needs no exclusive lock, a write needs both empty
BeginServe ==
  /\ queue # <<>>
  /\ writing = {}
  /\ LET head == Head(queue) IN
       \/ (head.kind = "read" /\ reading' = reading \cup {head.pid})
       \/ (head.kind = "write" /\ reading = {} /\ writing' = {head.pid})
  /\ queue' = Tail(queue)

StopActivity(p) ==
  \/ \E q \in reading : reading' = reading \ {q}
  \/ \E q \in writing : writing' = writing \ {q}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in Actors : RequestRead(p)
  \/ \E p \in Actors : RequestWrite(p)
  \/ BeginServe
  \/ \E p \in Actors : StopActivity(p)

Spec == Init /\ [][Next]_vars
        /\ (\A p \in Actors : WF_vars(RequestRead(p)))
        /\ (\A p \in Actors : WF_vars(RequestWrite(p)))
        /\ WF_vars(BeginServe)
        /\ (\A p \in Actors : WF_vars(StopActivity(p)))

\* Safety: readers and writers never active together, and at most one writer
Safety ==
  /\ (writing # {} => reading = {})
  /\ \A w1, w2 \in writing : w1 = w2

\* Liveness: every process eventually gets to read and to write, and any active
\* read/write eventually stops -- no process is starved of access
Liveness ==
  /\ \A p \in Actors : <>(p \in reading)
  /\ \A p \in Actors : <>(p \in writing)
  /\ \A p \in Actors : (p \in reading) ~> (p \notin reading)
  /\ \A p \in Actors : (p \in writing) ~> (p \notin writing)

====