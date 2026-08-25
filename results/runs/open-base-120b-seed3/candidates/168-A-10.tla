---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

\* The set of actor identifiers (provided by the .cfg as a substitution for NumActors)
n == 1 .. NumActors

VARIABLES Readers, Writers, Queue

\* ------------------------------------------------------------------------
\* Types
\* ------------------------------------------------------------------------
Request == [proc : n, type : {"read", "write"}]

TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Queue \in Seq(Request)

\* ------------------------------------------------------------------------
\* Initial state
\* ------------------------------------------------------------------------
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = <<>>

\* ------------------------------------------------------------------------
\* Actions
\* ------------------------------------------------------------------------
RequestRead ==
    \E p \in n :
        /\ p \notin Readers
        /\ p \notin Writers
        /\ ~(\E q \in Queue : q.proc = p)   \* not already waiting
        /\ Queue' = Append(Queue, [proc |-> p, type |-> "read"])
        /\ Readers' = Readers
        /\ Writers' = Writers

RequestWrite ==
    \E p \in n :
        /\ p \notin Readers
        /\ p \notin Writers
        /\ ~(\E q \in Queue : q.proc = p)   \* not already waiting
        /\ Queue' = Append(Queue, [proc |-> p, type |-> "write"])
        /\ Readers' = Readers
        /\ Writers' = Writers

ProcessQueue ==
    /\ Queue # <<>>                         \* non‑empty queue
    /\ LET head == Queue[1] IN
         /\ (head.type = "read")
            \/ (head.type = "write" /\ Readers = {})
    /\ Writers = {}                         \* no writer currently active
    /\ LET head == Queue[1] IN
         IF head.type = "read" THEN
             /\ Readers' = Readers \cup {head.proc}
             /\ Writers' = Writers
         ELSE
             /\ Readers' = Readers
             /\ Writers' = Writers \cup {head.proc}
    /\ Queue' = Tail(Queue)

Stop ==
    \E p \in n :
        /\ p \in Readers \/ p \in Writers
        /\ IF p \in Readers THEN
               Readers' = Readers \ {p}
               /\ Writers' = Writers
           ELSE
               Readers' = Readers
               /\ Writers' = Writers \ {p}
        /\ Queue' = Queue

\* ------------------------------------------------------------------------
\* Next-state relation
\* ------------------------------------------------------------------------
Next ==
    \/ RequestRead
    \/ RequestWrite
    \/ ProcessQueue
    \/ Stop

vars == <<Readers, Writers, Queue>>

\* ------------------------------------------------------------------------
\* Specification
\* ------------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars
          /\ WF_vars(RequestRead)
          /\ WF_vars(RequestWrite)
          /\ WF_vars(ProcessQueue)
          /\ WF_vars(Stop)

\* ------------------------------------------------------------------------
\* Safety properties
\* ------------------------------------------------------------------------
Safety ==
    /\ (Writers = {} \/ Readers = {})          \* no simultaneous readers & writers
    /\ Cardinality(Writers) <= 1               \* at most one writer

\* ------------------------------------------------------------------------
\* Liveness property
\* ------------------------------------------------------------------------
Liveness ==
    /\ \A p \in n : <> (p \in Readers)            \* eventually reads
    /\ \A p \in n : <> (p \in Writers)            \* eventually writes
    /\ \A p \in n : [] (p \in Readers => <> (p \notin Readers))  \* readers stop
    /\ \A p \in n : [] (p \in Writers => <> (p \notin Writers))  \* writers stop

====