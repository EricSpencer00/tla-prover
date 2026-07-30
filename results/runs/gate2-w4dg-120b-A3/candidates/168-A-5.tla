---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

\* Number of distinct actor processes.  The .cfg binds n (below) to a concrete
\* value (e.g. 2 or 3) for model checking.
CONSTANTS NumActors

Actors == 0 .. (NumActors - 1)
Modes == {"read", "write"}
Active == "active"
QueueRange == 1 .. NumActors

VARIABLES readers, writers, queue
vars == <<readers, writers, queue>>

TypeOK ==
  /\ readers \subseteq Actors
  /\ writers \subseteq Actors
  /\ queue \in Seq([actor: Actors, mode: Modes])

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

\* A process not yet waiting may request read access; it joins the FIFO queue.
RequestRead(p) ==
  /\ \A i \in 1..Len(queue): queue[i].actor # p
  /\ queue' = Append(queue, [actor |-> p, mode |-> "read"])
  /\ UNCHANGED <<readers, writers>>

\* A process not yet waiting may request write access; it joins the FIFO queue.
RequestWrite(p) ==
  /\ \A i \in 1..Len(queue): queue[i].actor # p
  /\ queue' = Append(queue, [actor |-> p, mode |-> "write"])
  /\ UNCHANGED <<readers, writers>>

\* The head of the queue is processed only once exclusive access allows.
Begin ==
  /\ queue # <<>>
  /\ writers = {}
  /\ LET req == Head(queue) IN
       /\ IF req.mode = "read"
          THEN readers' = readers \cup {req.actor}
               /\ writers' = writers
          ELSE writers' = writers \cup {req.actor}
               /\ readers' = readers
       /\ queue' = Tail(queue)

\* A process stops reading or writing voluntarily.
Stop(p) ==
  /\ (p \in readers \/ p \in writers)
  /\ readers' = readers \ {p}
  /\ writers' = writers \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in Actors: RequestRead(p)
  \/ \E p \in Actors: RequestWrite(p)
  \/ Begin
  \/ \E p \in Actors: Stop(p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in Actors: RequestRead(p))
        /\ WF_vars(\E p \in Actors: RequestWrite(p))
        /\ WF_vars(Begin)
        /\ WF_vars(\E p \in Actors: Stop(p))

\* Readers and writers are never simultaneously active.
Safety ==
  /\ (readers # {} => writers = {})
  /\ (writers # {} => readers = {})

\* No two writers are active at the same time.
NoDoubleWriter == Cardinality(writers) <= 1

Liveness ==
  /\ \A p \in Actors: (p \in readers) ~> (p \notin readers)
  /\ \A p \in Actors: (p \in writers) ~> (p \notin writers)

\* The .cfg substitutes a concrete value for n; n is treated as NumActors here.
n == NumActors

Spec == Spec
TypeOK == TypeOK
Safety == Safety
Liveness == Liveness
====