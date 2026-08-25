---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS NumActors

\* The set of actor identifiers (overridden by the .cfg)
n == 1 .. NumActors

VARIABLES Readers, Writers, Queue

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
WaitingProcs == { q.proc : q \in Queue }

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
    /\ p \notin Readers
    /\ p \notin Writers
    /\ p \notin WaitingProcs
    /\ Readers' = Readers
    /\ Writers' = Writers
    /\ Queue'   = Append(Queue, [proc |-> p, type |-> "read"])

RequestWrite(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ p \notin WaitingProcs
    /\ Readers' = Readers
    /\ Writers' = Writers
    /\ Queue'   = Append(Queue, [proc |-> p, type |-> "write"])

BeginRead ==
    /\ Queue # <<>>
    /\ Head(Queue).type = "read"
    /\ Writers = {}
    /\ Readers' = Readers \cup { Head(Queue).proc }
    /\ Writers' = Writers
    /\ Queue'   = Tail(Queue)

BeginWrite ==
    /\ Queue # <<>>
    /\ Head(Queue).type = "write"
    /\ Writers = {}
    /\ Readers = {}
    /\ Writers' = Writers \cup { Head(Queue).proc }
    /\ Readers' = Readers
    /\ Queue'   = Tail(Queue)

Stop ==
    \/ \E p \in Readers :
          /\ Readers' = Readers \ {p}
          /\ Writers' = Writers
          /\ Queue'   = Queue
    \/ \E p \in Writers :
          /\ Writers' = Writers \ {p}
          /\ Readers' = Readers
          /\ Queue'   = Queue

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in n : RequestRead(p)
    \/ \E p \in n : RequestWrite(p)
    \/ BeginRead
    \/ BeginWrite
    \/ Stop

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<Readers, Writers, Queue>>
    /\ WF_<<Readers, Writers, Queue>>( \E p \in n : RequestRead(p) )
    /\ WF_<<Readers, Writers, Queue>>( \E p \in n : RequestWrite(p) )
    /\ WF_<<Readers, Writers, Queue>>( BeginRead )
    /\ WF_<<Readers, Writers, Queue>>( BeginWrite )
    /\ WF_<<Readers, Writers, Queue>>( Stop )

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Readers \cap Writers = {}
    /\ Queue \in Seq( [proc : n, type : {"read","write"}] )

\* ----------------------------------------------------------------------
\* Safety invariant (readers and writers never simultaneous, at most one writer)
\* ----------------------------------------------------------------------
Safety ==
    /\ (Writers = {} \/ Readers = {})
    /\ Cardinality(Writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness property: every process eventually reads and eventually writes
\* ----------------------------------------------------------------------
Liveness ==
    \A p \in n : (<> (p \in Readers) /\ <> (p \in Writers))

=============================================================================