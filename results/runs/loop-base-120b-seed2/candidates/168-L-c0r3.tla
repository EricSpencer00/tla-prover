---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors, n

\* ----------------------------------------------------------------------
\* Types
Req == { [proc |-> p, type |-> "read"]  : p \in n } \cup
       { [proc |-> p, type |-> "write"] : p \in n }

\* ----------------------------------------------------------------------
\* Variables
VARIABLES Readers, Writers, Queue

vars == << Readers, Writers, Queue >>

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = << >>

\* ----------------------------------------------------------------------
\* Actions

\* Request to read
RequestReadAct(p) ==
    /\ p \in n
    /\ ~(\E q \in Queue : q.proc = p)      \* not already waiting
    /\ Readers' = Readers
    /\ Writers' = Writers
    /\ Queue'   = Append(Queue, [proc |-> p, type |-> "read"])

RequestRead ==
    \E p \in n : RequestReadAct(p)

\* Request to write
RequestWriteAct(p) ==
    /\ p \in n
    /\ ~(\E q \in Queue : q.proc = p)      \* not already waiting
    /\ Readers' = Readers
    /\ Writers' = Writers
    /\ Queue'   = Append(Queue, [proc |-> p, type |-> "write"])

RequestWrite ==
    \E p \in n : RequestWriteAct(p)

\* Process the queue (first‑come‑first‑served)
ProcessQueue ==
    \/ /\ Len(Queue) > 0
       /\ Writers = {}
       /\ LET front == Head(Queue) IN
          /\ front.type = "read"
          /\ Readers' = Readers \cup { front.proc }
          /\ Writers' = Writers
          /\ Queue'   = Tail(Queue)
    \/ /\ Len(Queue) > 0
       /\ Writers = {}
       /\ Readers = {}
       /\ LET front == Head(Queue) IN
          /\ front.type = "write"
          /\ Readers' = Readers
          /\ Writers' = { front.proc }
          /\ Queue'   = Tail(Queue)

\* Stop activity (reading or writing)
StopAct(p) ==
    /\ p \in n
    /\ (p \in Readers) \/ (p \in Writers)
    /\ Queue' = Queue
    /\ IF p \in Readers
          THEN /\ Readers' = Readers \ {p}
               /\ Writers' = Writers
          ELSE /\ Readers' = Readers
               /\ Writers' = Writers \ {p}

Stop ==
    \E p \in n : StopAct(p)

\* ----------------------------------------------------------------------
\* Next-state relation
Next ==
    \/ RequestRead
    \/ RequestWrite
    \/ ProcessQueue
    \/ Stop

\* ----------------------------------------------------------------------
\* Specification
Spec ==
    Init /\ [][Next]_vars
        /\ WF_vars(RequestRead)
        /\ WF_vars(RequestWrite)
        /\ WF_vars(ProcessQueue)
        /\ WF_vars(Stop)

\* ----------------------------------------------------------------------
\* Invariants

TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Queue \in Seq(Req)

Safety ==
    /\ (Writers = {} \/ Readers = {})          \* readers and writers never overlap
    /\ Cardinality(Writers) <= 1               \* at most one writer

\* ----------------------------------------------------------------------
\* Liveness property
Liveness ==
    /\ \A p \in n :
          (<> (p \in Readers))               \* every process eventually reads
          /\ (<> (p \in Writers))            \* every process eventually writes
    /\ \A p \in n :
          [] (p \in Readers => <> (p \notin Readers))   \* readers eventually stop
          /\ [] (p \in Writers => <> (p \notin Writers)) \* writers eventually stop

====