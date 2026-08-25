---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\* Derived constant used by the .cfg file (substituted for NumActors)
\* ----------------------------------------------------------------------
n == 1 .. NumActors

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Request == [type : {"read", "write"}, proc : n]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES readers, writers, queue

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
vars == << readers, writers, queue >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = << >>

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
ReqRead(p) ==
    /\ p \in n
    /\ p \notin readers
    /\ p \notin writers
    /\ ~(\E q \in queue : q.proc = p)        \* not already waiting
    /\ queue' = Append(queue, <<[type |-> "read",  proc |-> p]>>)
    /\ UNCHANGED << readers, writers >>

ReqWrite(p) ==
    /\ p \in n
    /\ p \notin readers
    /\ p \notin writers
    /\ ~(\E q \in queue : q.proc = p)        \* not already waiting
    /\ queue' = Append(queue, <<[type |-> "write", proc |-> p]>>)
    /\ UNCHANGED << readers, writers >>

BeginRead ==
    /\ queue # <<>>
    /\ queue[1].type = "read"
    /\ readers' = readers \cup { queue[1].proc }
    /\ writers' = writers
    /\ queue'   = Tail(queue)
    /\ UNCHANGED << >>

BeginWrite ==
    /\ queue # <<>>
    /\ queue[1].type = "write"
    /\ readers = {}
    /\ writers' = { queue[1].proc }
    /\ queue'   = Tail(queue)
    /\ UNCHANGED << >>

ProcQueue == BeginRead \/ BeginWrite

Stop(p) ==
    /\ (p \in readers) \/ (p \in writers)
    /\ readers' = readers \ {p}
    /\ writers' = IF p \in writers THEN {} ELSE writers
    /\ UNCHANGED queue

\* ----------------------------------------------------------------------
\* Action aggregations used for fairness
\* ----------------------------------------------------------------------
RequestRead  == \E p \in n : ReqRead(p)
RequestWrite == \E p \in n : ReqWrite(p)
StopAction   == \E p \in n : Stop(p)

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ RequestRead
    \/ RequestWrite
    \/ ProcQueue
    \/ StopAction

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars
        /\ WF_vars(RequestRead)
        /\ WF_vars(RequestWrite)
        /\ WF_vars(ProcQueue)
        /\ WF_vars(StopAction)

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ readers \subseteq n
    /\ writers \subseteq n
    /\ Cardinality(writers) <= 1
    /\ queue \in Seq(Request)

\* ----------------------------------------------------------------------
\* Safety invariant (mutual exclusion)
\* ----------------------------------------------------------------------
Safety ==
    /\ (writers = {} \/ readers = {})
    /\ Cardinality(writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness properties
\* ----------------------------------------------------------------------
Liveness ==
    /\ []<>(\A p \in n : <> (p \in readers))      \* every process eventually reads
    /\ []<>(\A p \in n : <> (p \in writers))      \* every process eventually writes
    /\ []<>(\A p \in n : (p \in readers) => <> (p \notin readers)) \* readers eventually stop
    /\ []<>(\A p \in n : (p \in writers) => <> (p \notin writers)) \* writers eventually stop

=============================================================================