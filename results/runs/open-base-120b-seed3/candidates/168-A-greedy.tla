---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\* Derived constant used by the .cfg file (substituted for NumActors)
\* ----------------------------------------------------------------------
n == 1 .. NumActors

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES readers, writers, queue

vars == << readers, writers, queue >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
IsRequest(r) == 
    /\ r \in [proc : n, type : {"read", "write"}]

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
ReadReq(p) ==
    /\ p \in n
    /\ ~(\E i \in 1 .. Len(queue) : queue[i].proc = p)   \* not already waiting
    /\ queue' = Append(queue, [proc |-> p, type |-> "read"])
    /\ UNCHANGED << readers, writers >>

WriteReq(p) ==
    /\ p \in n
    /\ ~(\E i \in 1 .. Len(queue) : queue[i].proc = p)   \* not already waiting
    /\ queue' = Append(queue, [proc |-> p, type |-> "write"])
    /\ UNCHANGED << readers, writers >>

ProcessQueue ==
    /\ Len(queue) > 0
    /\ writers = {}                                          \* no writer active
    /\ LET front == queue[1] IN
       IF front.type = "read" THEN
          /\ readers' = readers \cup {front.proc}
          /\ writers' = writers
          /\ queue'   = Tail(queue)
       ELSE
          /\ readers = {}                                    \* no readers for a write
          /\ writers' = {front.proc}
          /\ queue'   = Tail(queue)
    /\ UNCHANGED readers   \* when a write starts, readers already = {}
    /\ UNCHANGED writers   \* when a read starts, writers already = {}

Stop(p) ==
    /\ p \in n
    /\ \/ p \in readers
          /\ readers' = readers \ {p}
          /\ UNCHANGED << writers, queue >>
       \/ p \in writers
          /\ writers' = {}
          /\ UNCHANGED << readers, queue >>
    /\ ~ (p \in readers \/ p \in writers) => UNCHANGED vars

Next ==
    \/ \E p \in n: ReadReq(p)
    \/ \E p \in n: WriteReq(p)
    \/ ProcessQueue
    \/ \E p \in n: Stop(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars
    /\ \A p \in n: WF_vars(ReadReq(p))
    /\ \A p \in n: WF_vars(WriteReq(p))
    /\ WF_vars(ProcessQueue)
    /\ \A p \in n: WF_vars(Stop(p))

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ readers \subseteq n
    /\ writers \subseteq n
    /\ Cardinality(writers) <= 1
    /\ IsSeq(queue)
    /\ \A i \in 1 .. Len(queue) : IsRequest(queue[i])

\* ----------------------------------------------------------------------
\* Safety invariant (no simultaneous readers and writers, at most one writer)
\* ----------------------------------------------------------------------
Safety ==
    /\ (writers = {} \/ readers = {})
    /\ Cardinality(writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Liveness ==
    /\ \A p \in n : <> (p \in readers)          \* every process eventually reads
    /\ \A p \in n : <> (p \in writers)          \* every process eventually writes
    /\ \A p \in n : [] (p \in readers => <> (p \notin readers))   \* readers eventually stop
    /\ \A p \in n : [] (p \in writers => <> (p \notin writers))   \* writers eventually stop

====