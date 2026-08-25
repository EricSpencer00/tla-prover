---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\* Derived constant: the finite set of actor identifiers
\* The model checker will substitute a concrete value for n via the .cfg file
\* ----------------------------------------------------------------------
n == 1 .. NumActors

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Proc == n
Access == [proc : Proc, type : {"read", "write"}]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES readers, writers, queue

vars == << readers, writers, queue >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
QueueProcs == { q.proc : q \in queue }

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
    /\ p \in Proc
    /\ p \notin readers
    /\ p \notin writers
    /\ p \notin QueueProcs
    /\ queue' = Append(queue, [proc |-> p, type |-> "read"])
    /\ UNCHANGED << readers, writers >>

ReqWrite(p) ==
    /\ p \in Proc
    /\ p \notin readers
    /\ p \notin writers
    /\ p \notin QueueProcs
    /\ queue' = Append(queue, [proc |-> p, type |-> "write"])
    /\ UNCHANGED << readers, writers >>

ProcessQueue ==
    \/ /\ queue # <<>>
       /\ Head(queue).type = "read"
       /\ writers = {}
       /\ readers' = readers \cup {Head(queue).proc}
       /\ writers' = writers
       /\ queue'   = Tail(queue)
    \/ /\ queue # <<>>
       /\ Head(queue).type = "write"
       /\ writers = {}
       /\ readers = {}
       /\ writers' = writers \cup {Head(queue).proc}
       /\ readers' = readers
       /\ queue'   = Tail(queue)

StopAct(p) ==
    /\ p \in Proc
    /\ (p \in readers \/ p \in writers)
    /\ IF p \in readers
          THEN readers' = readers \ {p}
                /\ writers' = writers
       ELSE readers' = readers
                /\ writers' = writers \ {p}
    /\ UNCHANGED queue

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : ReqRead(p)
    \/ \E p \in Proc : ReqWrite(p)
    \/ ProcessQueue
    \/ \E p \in Proc : StopAct(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars
    /\ WF_vars(\E p \in Proc : ReqRead(p))
    /\ WF_vars(\E p \in Proc : ReqWrite(p))
    /\ WF_vars(ProcessQueue)
    /\ WF_vars(\E p \in Proc : StopAct(p))

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ readers \subseteq Proc
    /\ writers \subseteq Proc
    /\ readers \cap writers = {}
    /\ \A a \in queue : a \in Access
    /\ Len(queue) >= 0

\* ----------------------------------------------------------------------
\* Safety invariant (readers and writers never active together,
\* at most one writer)
\* ----------------------------------------------------------------------
Safety ==
    /\ (writers = {} \/ readers = {})
    /\ Cardinality(writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness property
\*   - every process eventually reads and eventually writes
\*   - any active reader or writer eventually stops
\* ----------------------------------------------------------------------
Liveness ==
    \A p \in Proc :
        /\ <> (p \in readers)          \* eventually gets to read
        /\ <> (p \in writers)          \* eventually gets to write
        /\ [] (p \in readers => <> (p \notin readers))   \* reading stops
        /\ [] (p \in writers => <> (p \notin writers))   \* writing stops

====