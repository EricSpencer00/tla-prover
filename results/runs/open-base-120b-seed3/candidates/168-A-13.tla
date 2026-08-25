---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\* Derived sets and types
\* ----------------------------------------------------------------------
n == 1 .. NumActors                     \* used by the .cfg as a bounded version of NumActors
Actors == n

Req == [pid : Actors, op : {"Read", "Write"}]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Readers, Writers, Queue

vars == <<Readers, Writers, Queue>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Readers \in SUBSET Actors
  /\ Writers \in SUBSET Actors
  /\ Queue   \in Seq(Req)

\* ----------------------------------------------------------------------
\* Safety invariant (mutual exclusion and at most one writer)
\* ----------------------------------------------------------------------
Safety ==
  /\ (Writers = {} \/ Readers = {})
  /\ Cardinality(Writers) <= 1

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Readers = {}
  /\ Writers = {}
  /\ Queue   = <<>>

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
RequestRead(p) ==
  /\ p \in Actors
  /\ p \notin Readers
  /\ p \notin Writers
  /\ ~(\E q \in Queue : q.pid = p /\ q.op = "Read")
  /\ Readers' = Readers
  /\ Writers' = Writers
  /\ Queue'   = Queue \o <<[pid |-> p, op |-> "Read"]>>

RequestWrite(p) ==
  /\ p \in Actors
  /\ p \notin Readers
  /\ p \notin Writers
  /\ ~(\E q \in Queue : q.pid = p /\ q.op = "Write")
  /\ Readers' = Readers
  /\ Writers' = Writers
  /\ Queue'   = Queue \o <<[pid |-> p, op |-> "Write"]>>

BeginRead ==
  /\ Queue # <<>>
  /\ Head(Queue).op = "Read"
  /\ Readers' = Readers \cup {Head(Queue).pid}
  /\ Writers' = Writers
  /\ Queue'   = Tail(Queue)

BeginWrite ==
  /\ Queue # <<>>
  /\ Head(Queue).op = "Write"
  /\ Readers = {}
  /\ Writers = {}
  /\ Writers' = {Head(Queue).pid}
  /\ Readers' = Readers
  /\ Queue'   = Tail(Queue)

Stop(p) ==
  /\ p \in Actors
  /\ \/ p \in Readers
        /\ Readers' = Readers \ {p}
        /\ Writers' = Writers
        /\ Queue'   = Queue
     \/ p \in Writers
        /\ Writers' = {}
        /\ Readers' = Readers
        /\ Queue'   = Queue

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in Actors : RequestRead(p)
  \/ \E p \in Actors : RequestWrite(p)
  \/ BeginRead
  \/ BeginWrite
  \/ \E p \in Actors : Stop(p)

\* ----------------------------------------------------------------------
\* Fairness (weak fairness for all actions)
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_vars
    /\ WF_vars(RequestRead)
    /\ WF_vars(RequestWrite)
    /\ WF_vars(BeginRead)
    /\ WF_vars(BeginWrite)
    /\ WF_vars(Stop)

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Liveness ==
  /\ \A p \in Actors : <> (p \in Readers)      \* every process eventually reads
  /\ \A p \in Actors : <> (p \in Writers)      \* every process eventually writes
  /\ \A p \in Actors : [](p \in Readers => <> (p \notin Readers))  \* readers eventually stop
  /\ \A p \in Actors : [](p \in Writers => <> (p \notin Writers))  \* writers eventually stop

\* ----------------------------------------------------------------------
\* Theorem statements (optional, but keep identifiers)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Safety
THEOREM Spec => Liveness

====