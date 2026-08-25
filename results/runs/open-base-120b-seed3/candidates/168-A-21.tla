---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\* Derived constant: the set of actor identifiers
\* ----------------------------------------------------------------------
n == 1 .. NumActors

VARIABLES Readers, Writers, Queue

\* ----------------------------------------------------------------------
\* State predicates
\* ----------------------------------------------------------------------
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = <<>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
IsReadReq(e) == e.type = "read"
IsWriteReq(e) == e.type = "write"

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
ReadReq ==
    \E p \in n :
        /\ p \notin Readers
        /\ p \notin Writers
        /\ \A q \in Queue : ~(q.proc = p /\ q.type = "read")
        /\ Readers' = Readers
        /\ Writers' = Writers
        /\ Queue'   = Append(Queue, [proc |-> p, type |-> "read"])

WriteReq ==
    \E p \in n :
        /\ p \notin Readers
        /\ p \notin Writers
        /\ \A q \in Queue : ~(q.proc = p /\ q.type = "write")
        /\ Readers' = Readers
        /\ Writers' = Writers
        /\ Queue'   = Append(Queue, [proc |-> p, type |-> "write"])

Begin ==
    /\ Queue # <<>>                \* there is a pending request
    /\ Writers = {}                \* no writer currently active
    /\ LET front == Head(Queue) IN
           \/ /\ front.type = "read"
               /\ Readers' = Readers \cup {front.proc}
               /\ Writers' = Writers
               /\ Queue'   = Tail(Queue)
           \/ /\ front.type = "write"
               /\ Readers = {}     \* no readers while a writer starts
               /\ Readers' = Readers
               /\ Writers' = Writers \cup {front.proc}
               /\ Queue'   = Tail(Queue)

Stop ==
    \E p \in n :
        \/ /\ p \in Readers
           /\ Readers' = Readers \ {p}
           /\ Writers' = Writers
           /\ Queue'   = Queue
        \/ /\ p \in Writers
           /\ Writers' = Writers \ {p}
           /\ Readers' = Readers
           /\ Queue'   = Queue

Next == ReadReq \/ WriteReq \/ Begin \/ Stop

\* ----------------------------------------------------------------------
\* Variables tuple for stuttering
\* ----------------------------------------------------------------------
vars == <<Readers, Writers, Queue>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars
        /\ WF_vars(ReadReq)
        /\ WF_vars(WriteReq)
        /\ WF_vars(Begin)
        /\ WF_vars(Stop)

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Disjoint(Readers, Writers)
    /\ Queue \in Seq([proc : n, type : {"read", "write"}])

\* ----------------------------------------------------------------------
\* Safety invariant
\* ----------------------------------------------------------------------
Safety ==
    /\ (Writers = {} \/ Readers = {})      \* no simultaneous readers & writers
    /\ Cardinality(Writers) <= 1          \* at most one writer

\* ----------------------------------------------------------------------
\* Liveness properties
\* ----------------------------------------------------------------------
Liveness ==
    /\ \A p \in n : <> (p \in Readers)                 \* every process eventually reads
    /\ \A p \in n : <> (p \in Writers)                 \* every process eventually writes
    /\ \A p \in n : [] (p \in Readers => <> (p \notin Readers))   \* readers eventually stop
    /\ \A p \in n : [] (p \in Writers => <> (p \notin Writers))   \* writers eventually stop

\* ----------------------------------------------------------------------
\* Exported identifiers required by the .cfg file
\* ----------------------------------------------------------------------
SPECIFICATION Spec
INVARIANTS TypeOK, Safety
PROPERTIES Liveness

====