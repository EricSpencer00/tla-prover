---- MODULE ReadersWriters ----
EXTENDS FiniteSets, Sequences, TLC

CONSTANTS NumActors

\* Alias that the .cfg file substitutes for NumActors
n == NumActors

VARIABLES readers, writers, queue

\*=================================================================
\* Types
\*=================================================================
IsRequest == [proc : n, op : {"read", "write"}]

\*=================================================================
\* State predicates
\*=================================================================
TypeOK ==
    /\ readers \subseteq n
    /\ writers \subseteq n
    /\ Cardinality(writers) <= 1
    /\ queue \in Seq(IsRequest)

Safety ==
    /\ (writers = {} \/ readers = {})      \* no simultaneous readers & writers
    /\ Cardinality(writers) <= 1           \* at most one writer

\*=================================================================
\* Initial state
\*=================================================================
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = << >>

\*=================================================================
\* Helper definitions
\*=================================================================
QueueProcs == { q.proc : q \in queue }

\*=================================================================
\* Actions
\*=================================================================
RequestRead(p) ==
    /\ p \in n
    /\ p \notin readers
    /\ p \notin writers
    /\ p \notin QueueProcs
    /\ queue' = Append(queue, [proc |-> p, op |-> "read"])
    /\ readers' = readers
    /\ writers' = writers

RequestWrite(p) ==
    /\ p \in n
    /\ p \notin readers
    /\ p \notin writers
    /\ p \notin QueueProcs
    /\ queue' = Append(queue, [proc |-> p, op |-> "write"])
    /\ readers' = readers
    /\ writers' = writers

BeginRead ==
    /\ queue # <<>>
    /\ Head(queue).op = "read"
    /\ writers = {}
    /\ readers' = readers \cup {Head(queue).proc}
    /\ writers' = writers
    /\ queue'   = Tail(queue)

BeginWrite ==
    /\ queue # <<>>
    /\ Head(queue).op = "write"
    /\ writers = {}
    /\ readers = {}
    /\ readers' = readers
    /\ writers' = {Head(queue).proc}
    /\ queue'   = Tail(queue)

ProcessQueue == BeginRead \/ BeginWrite

Stop(p) ==
    /\ p \in n
    /\ (p \in readers \/ p \in writers)
    /\ readers' = readers \ {p}
    /\ writers' = writers \ {p}
    /\ queue'   = queue

\* Parameter‑free actions for fairness specifications
RequestReadAction  == \E p \in n : RequestRead(p)
RequestWriteAction == \E p \in n : RequestWrite(p)
StopAction         == \E p \in n : Stop(p)

Next ==
    \/ RequestReadAction
    \/ RequestWriteAction
    \/ StopAction
    \/ ProcessQueue

\*=================================================================
\* Specification
\*=================================================================
vars == << readers, writers, queue >>

Spec ==
    Init /\
    [][Next]_vars /\
    WF_vars(RequestReadAction) /\
    WF_vars(RequestWriteAction) /\
    WF_vars(StopAction) /\
    WF_vars(ProcessQueue)

\*=================================================================
\* Invariants
\*=================================================================
INVARIANTS == TypeOK /\ Safety

\*=================================================================
\* Liveness property
\*=================================================================
Liveness ==
    \A p \in n :
        ( <> (p \in readers) /\ <> (p \in writers) )
        /\ ( [] (p \in readers => <> (p \notin readers)) )
        /\ ( [] (p \in writers => <> (p \notin writers)) )

=============================================================================