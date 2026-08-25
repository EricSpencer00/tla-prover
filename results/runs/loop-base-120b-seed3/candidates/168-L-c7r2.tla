---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\* Derived constant used by the .cfg file (substituted for NumActors)
\* ----------------------------------------------------------------------
n == 1 .. NumActors

VARIABLES Readers, Writers, Queue

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
vars == << Readers, Writers, Queue >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = << >>

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
RequestRead(p) ==
    /\ p \in n
    /\ ~(\E q \in Queue : q.pid = p /\ q.type = "read")
    /\ Readers' = Readers
    /\ Writers' = Writers
    /\ Queue'   = Append(Queue, [type |-> "read", pid |-> p])

RequestWrite(p) ==
    /\ p \in n
    /\ ~(\E q \in Queue : q.pid = p /\ q.type = "write")
    /\ Readers' = Readers
    /\ Writers' = Writers
    /\ Queue'   = Append(Queue, [type |-> "write", pid |-> p])

Begin ==
    /\ Queue # << >>
    /\ Writers = {}
    /\ LET front == Head(Queue) IN
       \/ /\ front.type = "read"
          /\ Readers' = Readers \cup {front.pid}
          /\ Writers' = Writers
          /\ Queue'   = Tail(Queue)
       \/ /\ front.type = "write"
          /\ Readers = {}
          /\ Writers' = {front.pid}
          /\ Readers' = Readers
          /\ Queue'   = Tail(Queue)

Stop(p) ==
    /\ p \in Readers \/ p \in Writers
    /\ Readers' = IF p \in Readers THEN Readers \ {p} ELSE Readers
    /\ Writers' = IF p \in Writers THEN Writers \ {p} ELSE Writers
    /\ Queue'   = Queue

\* ----------------------------------------------------------------------
\* Composite actions for fairness constraints
\* ----------------------------------------------------------------------
RequestReadAct == \E p \in n : RequestRead(p)
RequestWriteAct == \E p \in n : RequestWrite(p)
StopAct == \E p \in n : Stop(p)

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    RequestReadAct \/ RequestWriteAct \/ StopAct \/ Begin

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars
    /\ (\A p \in n : WF_vars(RequestRead(p)))
    /\ (\A p \in n : WF_vars(RequestWrite(p)))
    /\ (\A p \in n : WF_vars(Stop(p)))
    /\ WF_vars(Begin)

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ \A q \in Queue : q \in [type : {"read","write"}, pid : n]

\* ----------------------------------------------------------------------
\* Safety invariant
\* ----------------------------------------------------------------------
Safety ==
    /\ (Writers = {} \/ Readers = {})
    /\ Cardinality(Writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Liveness ==
    \A p \in n :
        <> (p \in Readers) /\ <> (p \in Writers) /\
        <> (p \notin Readers) /\ <> (p \notin Writers)

=============================================================================