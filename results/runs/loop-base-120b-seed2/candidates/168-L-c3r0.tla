---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\*  Derived constant used by the .cfg file (substituted for NumActors)
\* ----------------------------------------------------------------------
n == 1..NumActors

VARIABLES Readers, Writers, Queue

\* ----------------------------------------------------------------------
\*  Types
\* ----------------------------------------------------------------------
Req == [proc : n, type : {"read", "write"}]

\* ----------------------------------------------------------------------
\*  Helper definitions
\* ----------------------------------------------------------------------
vars == << Readers, Writers, Queue >>

Pending == { q.proc : q \in SeqToSet(Queue) }

\* ----------------------------------------------------------------------
\*  Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = <<>>

\* ----------------------------------------------------------------------
\*  Actions
\* ----------------------------------------------------------------------
RequestRead(p) ==
    /\ p \in n
    /\ p \notin Pending
    /\ Queue' = Append(Queue, [proc |-> p, type |-> "read"])
    /\ UNCHANGED << Readers, Writers >>

RequestWrite(p) ==
    /\ p \in n
    /\ p \notin Pending
    /\ Queue' = Append(Queue, [proc |-> p, type |-> "write"])
    /\ UNCHANGED << Readers, Writers >>

ProcessQueue ==
    /\ Queue # <<>>
    /\ LET front == Head(Queue) IN
        \/ /\ front.type = "read"
           /\ Writers = {}
           /\ Readers' = Readers \cup {front.proc}
           /\ Writers' = Writers
           /\ Queue'   = Tail(Queue)
        \/ /\ front.type = "write"
           /\ Readers = {}
           /\ Writers' = Writers \cup {front.proc}
           /\ Readers' = Readers
           /\ Queue'   = Tail(Queue)

Stop(p) ==
    \/ /\ p \in Readers
       /\ Readers' = Readers \ {p}
       /\ UNCHANGED << Writers, Queue >>
    \/ /\ p \in Writers
       /\ Writers' = Writers \ {p}
       /\ UNCHANGED << Readers, Queue >>

Next ==
    \/ \E p \in n: RequestRead(p)
    \/ \E p \in n: RequestWrite(p)
    \/ ProcessQueue
    \/ \E p \in n: Stop(p)

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars
    /\ \A p \in n: WF_vars(RequestRead(p))
    /\ \A p \in n: WF_vars(RequestWrite(p))
    /\ WF_vars(ProcessQueue)
    /\ \A p \in n: WF_vars(Stop(p))

\* ----------------------------------------------------------------------
\*  Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Queue \in Seq(Req)

Safety ==
    /\ (Writers = {} \/ Readers = {})
    /\ Cardinality(Writers) <= 1

\* ----------------------------------------------------------------------
\*  Liveness property
\* ----------------------------------------------------------------------
Liveness ==
    /\ \A p \in n: <> (p \in Readers)
    /\ \A p \in n: <> (p \in Writers)
    /\ \A p \in n: [] (p \in Readers => <> (p \notin Readers))
    /\ \A p \in n: [] (p \in Writers => <> (p \notin Writers))

\* ----------------------------------------------------------------------
\*  Exported identifiers required by the .cfg file
\* ----------------------------------------------------------------------
SPECIFICATION Spec
INVARIANTS TypeOK, Safety
PROPERTIES Liveness

====