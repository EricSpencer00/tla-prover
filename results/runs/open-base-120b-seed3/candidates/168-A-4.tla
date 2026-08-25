---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT NumActors

\* ----------------------------------------------------------------------
\* Derived constant: the finite set of actor identifiers
\* The model checker will substitute a concrete set for n via the .cfg file.
\* ----------------------------------------------------------------------
n == 1 .. NumActors

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Kind == {"Read", "Write"}

Req == [pid : n, kind : Kind]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES readers, writers, queue

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = << >>

\* ----------------------------------------------------------------------
\* Helper predicates
\* ----------------------------------------------------------------------
NotWaiting(p) ==
    ~∃ i \in 1 .. Len(queue) : queue[i].pid = p

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
RequestRead(p) ==
    /\ p \in n
    /\ p \notin readers
    /\ p \notin writers
    /\ NotWaiting(p)
    /\ readers' = readers
    /\ writers' = writers
    /\ queue'   = queue \o <<[pid |-> p, kind |-> "Read"]>>
    /\ UNCHANGED << >>

RequestWrite(p) ==
    /\ p \in n
    /\ p \notin readers
    /\ p \notin writers
    /\ NotWaiting(p)
    /\ readers' = readers
    /\ writers' = writers
    /\ queue'   = queue \o <<[pid |-> p, kind |-> "Write"]>>
    /\ UNCHANGED << >>

ProcessQueue ==
    \/ /\ Len(queue) > 0
       /\ Head(queue).kind = "Read"
       /\ writers = {}
       /\ readers' = readers \cup {Head(queue).pid}
       /\ writers' = writers
       /\ queue'   = Tail(queue)
    \/ /\ Len(queue) > 0
       /\ Head(queue).kind = "Write"
       /\ writers = {}
       /\ readers = {}
       /\ writers' = {Head(queue).pid}
       /\ readers' = readers
       /\ queue'   = Tail(queue)

Stop(p) ==
    /\ p \in n
    /\ (p \in readers) \/ (p \in writers)
    /\ readers' = IF p \in readers THEN readers \ {p} ELSE readers
    /\ writers' = IF p \in writers THEN writers \ {p} ELSE writers
    /\ queue'   = queue
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ ∃ p \in n : RequestRead(p)
    \/ ∃ p \in n : RequestWrite(p)
    \/ ProcessQueue
    \/ ∃ p \in n : Stop(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<readers, writers, queue>> /\
    WF_(∃ p \in n : RequestRead(p)) /\
    WF_(∃ p \in n : RequestWrite(p)) /\
    WF_(ProcessQueue) /\
    WF_(∃ p \in n : Stop(p))

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ readers \subseteq n
    /\ writers \subseteq n
    /\ Cardinality(writers) <= 1
    /\ queue \in Seq(Req)

\* ----------------------------------------------------------------------
\* Safety invariant
\* ----------------------------------------------------------------------
Safety ==
    /\ Disjoint(readers, writers)
    /\ Cardinality(writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness property
\*   - every process eventually reads and eventually writes
\*   - every active reader eventually stops reading
\*   - every active writer eventually stops writing
\* ----------------------------------------------------------------------
Liveness ==
    \A p \in n :
        ( <> (p \in readers)            /\   <> (p \in writers) ) /\
        ( [] (p \in readers => <> (p \notin readers)) ) /\
        ( [] (p \in writers => <> (p \notin writers)) )

\* ----------------------------------------------------------------------
\* Exported identifiers required by the .cfg file
\* ----------------------------------------------------------------------
CONSTANTS
    NumActors

SPECIFICATION Spec
INVARIANT TypeOK, Safety
PROPERTY Liveness

====