---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT NumActors

VARIABLES Readers, Writers, Queue

\* Definitions
Actors == 1 .. NumActors
ModeSet == {"R", "W"}
Request == [pid : Actors, mode : ModeSet]
QueueType == Seq(Request)

\* Initial state
Init ==
  /\ Readers = {}
  /\ Writers = {}
  /\ Queue = <<>>

\* Actions
RequestRead(p) ==
  /\ p \in Actors
  /\ \A q \in Queue : (q.pid # p \/ q.mode # "R")
  /\ Queue' = Append(Queue, [pid |-> p, mode |-> "R"])
  /\ UNCHANGED <<Readers, Writers>>

RequestWrite(p) ==
  /\ p \in Actors
  /\ \A q \in Queue : (q.pid # p \/ q.mode # "W")
  /\ Queue' = Append(Queue, [pid |-> p, mode |-> "W"])
  /\ UNCHANGED <<Readers, Writers>>

ProcessQueue ==
  /\ Queue # <<>>
  /\ Writers = {}
  /\ IF Head(Queue).mode = "R" THEN
        /\ Readers' = Readers \cup {Head(Queue).pid}
        /\ Writers' = Writers
        /\ Queue' = Tail(Queue)
     ELSE
        /\ Head(Queue).mode = "W"
        /\ Readers = {}
        /\ Readers' = Readers
        /\ Writers' = {Head(Queue).pid}
        /\ Queue' = Tail(Queue)

Stop(p) ==
  /\ p \in Readers \/ p \in Writers
  /\ IF p \in Readers THEN Readers' = Readers \ {p} ELSE Readers' = Readers
  /\ IF p \in Writers THEN Writers' = {} ELSE Writers' = Writers
  /\ UNCHANGED Queue

Next ==
  \/ \E p \in Actors : RequestRead(p)
  \/ \E p \in Actors : RequestWrite(p)
  \/ ProcessQueue
  \/ \E p \in Actors : Stop(p)

\* Specification
Spec == Init /\ [][Next]_<<Readers, Writers, Queue>>

\* Type correctness invariant
TypeOK ==
  /\ Readers \subseteq Actors
  /\ Writers \subseteq Actors
  /\ \Cardinality(Writers) <= 1
  /\ Queue \in Seq(Request)
  /\ \A q \in Queue : q.pid \in Actors /\ q.mode \in ModeSet

\* Safety invariant
Safety ==
  /\ \A p \in Writers : p \notin Readers
  /\ \Cardinality(Writers) <= 1

\* Liveness property
Liveness ==
  /\ \A p \in Actors : [] (p \in Readers => <> (p \notin Readers))
  /\ \A p \in Actors : [] (p \in Writers => <> (p \notin Writers))
  /\ \A p \in Actors : [] <> (p \in Readers)
  /\ \A p \in Actors : [] <> (p \in Writers)

CHECK_DEADLOCK FALSE

====