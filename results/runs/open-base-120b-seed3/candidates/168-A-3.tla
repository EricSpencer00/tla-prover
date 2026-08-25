---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

\* The set of actor identifiers (will be instantiated in the .cfg)
n == 1 .. NumActors

VARIABLES Readers, Writers, Queue

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
IsRequest(r) == 
    /\ r \in [proc: n, type: {"read", "write"}]

IsQueue(q) == q \in Seq( [proc: n, type: {"read", "write"}] )

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue = << >>

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
RequestRead(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ \A r \in Queue : r.proc # p
    /\ Queue' = Append(Queue, [proc |-> p, type |-> "read"])
    /\ UNCHANGED << Readers, Writers >>

RequestWrite(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ \A r \in Queue : r.proc # p
    /\ Queue' = Append(Queue, [proc |-> p, type |-> "write"])
    /\ UNCHANGED << Readers, Writers >>

\* Process the request at the head of the queue, if possible
ProcessQueue ==
    /\ Queue # << >>
    /\ LET r == Head(Queue) IN
       /\ IF r.type = "read" THEN
              /\ Writers = {}
              /\ Readers' = Readers \cup {r.proc}
              /\ Writers' = Writers
              /\ Queue' = Tail(Queue)
          ELSE
              /\ Writers = {}
              /\ Readers = {}
              /\ Writers' = {r.proc}
              /\ Readers' = Readers
              /\ Queue' = Tail(Queue)
    /\ UNCHANGED << >>

StopActivity(p) ==
    /\ p \in n
    /\ \/ p \in Readers
          /\ Readers' = Readers \ {p}
          /\ Writers' = Writers
       \/ p \in Writers
          /\ Writers' = {}
          /\ Readers' = Readers
    /\ UNCHANGED Queue

\* Existentially quantified actions for fairness
RequestReadAction == \E p \in n : RequestRead(p)
RequestWriteAction == \E p \in n : RequestWrite(p)
StopActivityAction == \E p \in n : StopActivity(p)

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ RequestReadAction
    \/ RequestWriteAction
    \/ ProcessQueue
    \/ StopActivityAction

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<Readers, Writers, Queue>>
    /\ WF_<<Readers, Writers, Queue>>(RequestReadAction)
    /\ WF_<<Readers, Writers, Queue>>(RequestWriteAction)
    /\ WF_<<Readers, Writers, Queue>>(ProcessQueue)
    /\ WF_<<Readers, Writers, Queue>>(StopActivityAction)

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ IsQueue(Queue)

Safety ==
    /\ (Writers = {} \/ Readers = {})
    /\ Cardinality(Writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Liveness ==
    \A p \in n :
        <> (p \in Readers) /\ <> (p \in Writers)

=============================================================================