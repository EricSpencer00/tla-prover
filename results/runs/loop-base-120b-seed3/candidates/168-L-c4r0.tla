---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* Set of actor identifiers
n == 1..NumActors

VARIABLES Readers, Writers, Queue

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Req == [proc : n, kind : {"R", "W"}]

TypeOK == /\ Readers \subseteq n
          /\ Writers \subseteq n
          /\ Queue \in Seq(Req)

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Safety == /\ (Writers = {} \/ Readers = {})
          /\ Cardinality(Writers) <= 1

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == /\ Readers = {}
        /\ Writers = {}
        /\ Queue   = <<>>

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
RequestRead(p) ==
  /\ p \in n
  /\ p \notin Readers
  /\ p \notin Writers
  /\ \A q \in Queue : ~(q.proc = p /\ q.kind = "R")
  /\ Queue'   = Append(Queue, [proc |-> p, kind |-> "R"])
  /\ Readers' = Readers
  /\ Writers' = Writers

RequestWrite(p) ==
  /\ p \in n
  /\ p \notin Readers
  /\ p \notin Writers
  /\ \A q \in Queue : ~(q.proc = p /\ q.kind = "W")
  /\ Queue'   = Append(Queue, [proc |-> p, kind |-> "W"])
  /\ Readers' = Readers
  /\ Writers' = Writers

ProcessQueue ==
  /\ Queue # <<>>
  /\ LET front == Head(Queue) IN
        \/ /\ front.kind = "R"
            /\ Writers = {}
            /\ Readers' = Readers \cup {front.proc}
            /\ Writers' = Writers
            /\ Queue'   = Tail(Queue)
        \/ /\ front.kind = "W"
            /\ Readers = {}
            /\ Writers' = Writers \cup {front.proc}
            /\ Readers' = Readers
            /\ Queue'   = Tail(Queue)

Stop(p) ==
  /\ p \in n
  /\ (p \in Readers \/ p \in Writers)
  /\ Readers' = Readers \ {p}
  /\ Writers' = Writers \ {p}
  /\ Queue'   = Queue

Next ==
  \/ \E p \in n : RequestRead(p)
  \/ \E p \in n : RequestWrite(p)
  \/ ProcessQueue
  \/ \E p \in n : Stop(p)

vars == <<Readers, Writers, Queue>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_vars
        /\ \A p \in n : WF_vars(RequestRead(p))
        /\ \A p \in n : WF_vars(RequestWrite(p))
        /\ WF_vars(ProcessQueue)
        /\ \A p \in n : WF_vars(Stop(p))

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Liveness ==
  /\ \A p \in n : <> (p \in Readers)
  /\ \A p \in n : <> (p \in Writers)
  /\ \A p \in n : [] (p \in Readers => <> (p \notin Readers))
  /\ \A p \in n : [] (p \in Writers => <> (p \notin Writers))

====