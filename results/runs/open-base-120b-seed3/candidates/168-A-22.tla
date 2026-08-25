---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT NumActors

\* ----------------------------------------------------------------------
\* Derived constant used by the .cfg file
\* ----------------------------------------------------------------------
n == 1 .. NumActors

\* ----------------------------------------------------------------------
\* Process identifiers
\* ----------------------------------------------------------------------
Proc == n

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Req == [pid : Proc, type : {"Read", "Write"}]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Readers, Writers, Queue

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = <<>>

\* ----------------------------------------------------------------------
\* Action: a process requests a read
\* ----------------------------------------------------------------------
RequestRead(p) ==
    /\ p \in Proc
    /\ ~(\E i \in DOMAIN Queue : Queue[i].pid = p)  \* not already waiting
    /\ Queue' = Queue \o <<[pid |-> p, type |-> "Read"]>>
    /\ Readers' = Readers
    /\ Writers' = Writers

\* ----------------------------------------------------------------------
\* Action: a process requests a write
\* ----------------------------------------------------------------------
RequestWrite(p) ==
    /\ p \in Proc
    /\ ~(\E i \in DOMAIN Queue : Queue[i].pid = p)  \* not already waiting
    /\ Queue' = Queue \o <<[pid |-> p, type |-> "Write"]>>
    /\ Readers' = Readers
    /\ Writers' = Writers

\* ----------------------------------------------------------------------
\* Action: begin reading (first request in queue is a read and no writer active)
\* ----------------------------------------------------------------------
BeginRead ==
    /\ Queue # <<>>
    /\ Queue[1].type = "Read"
    /\ Writers = {}
    /\ Readers' = Readers \cup {Queue[1].pid}
    /\ Writers' = Writers
    /\ Queue'   = Tail(Queue)

\* ----------------------------------------------------------------------
\* Action: begin writing (first request in queue is a write, no readers or writers)
\* ----------------------------------------------------------------------
BeginWrite ==
    /\ Queue # <<>>
    /\ Queue[1].type = "Write"
    /\ Writers = {}
    /\ Readers = {}
    /\ Writers' = Writers \cup {Queue[1].pid}
    /\ Readers' = Readers
    /\ Queue'   = Tail(Queue)

\* ----------------------------------------------------------------------
\* Action: a process stops its current activity
\* ----------------------------------------------------------------------
Stop(p) ==
    /\ p \in Proc
    /\ (p \in Readers \/ p \in Writers)
    /\ IF p \in Readers
          THEN /\ Readers' = Readers \ {p}
               /\ Writers' = Writers
          ELSE /\ Readers' = Readers
               /\ Writers' = Writers \ {p}
    /\ Queue' = Queue

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : RequestRead(p)
    \/ \E p \in Proc : RequestWrite(p)
    \/ BeginRead
    \/ BeginWrite
    \/ \E p \in Proc : Stop(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<Readers, Writers, Queue>>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariant: type correctness
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Readers \subseteq Proc
    /\ Writers \subseteq Proc
    /\ Queue \in Seq(Req)

\* ----------------------------------------------------------------------
\* Invariant: safety (no simultaneous readers/writers and at most one writer)
\* ----------------------------------------------------------------------
Safety ==
    /\ (Writers = {} \/ Readers = {})
    /\ Cardinality(Writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness property
\*   - every process eventually reads and eventually writes
\*   - every active reader eventually stops, and every active writer eventually stops
\* ----------------------------------------------------------------------
Liveness ==
    \A p \in Proc :
        (<> (p \in Readers))               \/   \* eventually reads
        /\ (<> (p \in Writers))            \/   \* eventually writes
        /\ [] (p \in Readers => <> (p \notin Readers))  \* reader eventually stops
        /\ [] (p \in Writers => <> (p \notin Writers))  \* writer eventually stops

=============================================================================