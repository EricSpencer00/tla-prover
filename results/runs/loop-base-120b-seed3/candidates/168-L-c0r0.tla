---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\* Derived constant used by the .cfg file (substituted for NumActors)
n == 1 .. NumActors

\* ----------------------------------------------------------------------
\* Types
Req == [pid : n, type : {"read", "write"}]

\* ----------------------------------------------------------------------
\* Variables
VARIABLES Readers, Writers, Queue

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = <<>>

\* ----------------------------------------------------------------------
\* Helper definitions
NotInQueue(p) == 
    \A q \in Queue : q.pid # p

\* ----------------------------------------------------------------------
\* Actions

RequestRead(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ NotInQueue(p)
    /\ Queue' = Queue \o <<[pid |-> p, type |-> "read"]>>
    /\ UNCHANGED <<Readers, Writers>>

RequestWrite(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ NotInQueue(p)
    /\ Queue' = Queue \o <<[pid |-> p, type |-> "write"]>>
    /\ UNCHANGED <<Readers, Writers>>

BeginRead ==
    /\ Queue # <<>>
    /\ Head(Queue).type = "read"
    /\ Writers = {}
    /\ Readers' = Readers \cup {Head(Queue).pid}
    /\ Writers' = Writers
    /\ Queue'   = Tail(Queue)
    /\ UNCHANGED <<>>

BeginWrite ==
    /\ Queue # <<>>
    /\ Head(Queue).type = "write"
    /\ Writers = {}
    /\ Readers = {}
    /\ Writers' = Writers \cup {Head(Queue).pid}
    /\ Readers' = Readers
    /\ Queue'   = Tail(Queue)
    /\ UNCHANGED <<>>

StopActivity(p) ==
    /\ p \in n
    /\ \/ p \in Readers
          /\ Readers' = Readers \ {p}
          /\ Writers' = Writers
       \/ p \in Writers
          /\ Writers' = Writers \ {p}
          /\ Readers' = Readers
    /\ UNCHANGED Queue

\* ----------------------------------------------------------------------
\* Next-state relation
Next ==
    \/ \E p \in n : RequestRead(p)
    \/ \E p \in n : RequestWrite(p)
    \/ BeginRead
    \/ BeginWrite
    \/ \E p \in n : StopActivity(p)

\* ----------------------------------------------------------------------
\* Specification
vars == <<Readers, Writers, Queue>>
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Readers \cap Writers = {}
    /\ Queue \in Seq(Req)

\* ----------------------------------------------------------------------
\* Safety invariant
Safety ==
    /\ (Writers = {} \/ Readers = {})
    /\ Cardinality(Writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness property
Liveness ==
    \A p \in n :
        /\ [] (p \in Readers => <> (p \notin Readers))
        /\ [] (p \in Writers => <> (p \notin Writers))
        /\ <> (p \in Readers)
        /\ <> (p \in Writers)

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* (already defined above):
\*   CONSTANTS: NumActors
\*   SPECIFICATION: Spec
\*   INVARIANTS: TypeOK, Safety
\*   PROPERTIES: Liveness
\*   n (substituted for NumActors)

====