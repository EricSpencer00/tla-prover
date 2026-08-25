---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\* Alias for the set of actor ids (the .cfg file substitutes the value for n)
\* ----------------------------------------------------------------------
n == NumActors

VARIABLES readers, writers, queue

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* A request record
Request == [type : {"R","W"}, proc : n]

\* The set of processes currently present in the queue
InQueue(p) == \E i \in 1..Len(queue) : queue[i].proc = p

\* Well‑formedness of the queue
QueueOK == queue \in Seq(Request)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = <<>>

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
ReadRequest ==
    \E p \in n :
        /\ p \notin readers
        /\ p \notin writers
        /\ ~InQueue(p)
        /\ queue' = Append(queue, [type |-> "R", proc |-> p])
        /\ UNCHANGED <<readers, writers>>

WriteRequest ==
    \E p \in n :
        /\ p \notin readers
        /\ p \notin writers
        /\ ~InQueue(p)
        /\ queue' = Append(queue, [type |-> "W", proc |-> p])
        /\ UNCHANGED <<readers, writers>>

Begin ==
    /\ queue # <<>>
    LET first == queue[1] IN
        /\ IF first.type = "R" THEN
               /\ readers' = readers \cup {first.proc}
               /\ writers' = writers
           ELSE
               /\ readers = {}
               /\ writers' = {first.proc}
               /\ readers' = readers
        /\ queue' = Tail(queue)

Stop ==
    \E p \in n :
        /\ p \in readers \/ p \in writers
        /\ IF p \in readers THEN
               /\ readers' = readers \ {p}
               /\ writers' = writers
           ELSE
               /\ writers' = {}
               /\ readers' = readers
        /\ UNCHANGED queue

Next == ReadRequest \/ WriteRequest \/ Begin \/ Stop

\* ----------------------------------------------------------------------
\* Specification (with weak fairness for all actions)
\* ----------------------------------------------------------------------
vars == <<readers, writers, queue>>

Spec ==
    Init /\ [][Next]_vars
        /\ WF_vars(ReadRequest)
        /\ WF_vars(WriteRequest)
        /\ WF_vars(Begin)
        /\ WF_vars(Stop)

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ readers \subseteq n
    /\ writers \subseteq n
    /\ Cardinality(writers) <= 1
    /\ readers \cap writers = {}
    /\ QueueOK

\* ----------------------------------------------------------------------
\* Safety invariant (readers and writers never active together,
\* at most one writer)
\* ----------------------------------------------------------------------
Safety ==
    /\ (readers = {} \/ writers = {})
    /\ Cardinality(writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness properties
\* ----------------------------------------------------------------------
Liveness ==
    /\ \A p \in n : <> (p \in readers)       \* every process eventually reads
    /\ \A p \in n : <> (p \in writers)       \* every process eventually writes
    /\ \A p \in n : [] (p \in readers => <> (p \notin readers)) \* readers eventually stop
    /\ \A p \in n : [] (p \in writers => <> (p \notin writers)) \* writers eventually stop

====