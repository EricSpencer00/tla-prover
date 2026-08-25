---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\* Set of actor identifiers (will be instantiated by the .cfg file)
\* The .cfg substitutes n for NumActors, therefore n must be defined here.
\* It can be overridden in the configuration; the default definition below
\* simply uses a finite range based on NumActors.
\* ----------------------------------------------------------------------
n == 1..NumActors

VARIABLES readers, writers, queue

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of processes currently waiting in the queue
WaitingSet == { q.proc : q \in queue }

\* The state of all variables as a tuple (used for stuttering)
vars == << readers, writers, queue >>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ readers \in SUBSET n
    /\ writers \in SUBSET n
    /\ queue   \in Seq( [proc: n, type: {"Read","Write"}] )

\* ----------------------------------------------------------------------
\* Safety invariant: no simultaneous readers and writers,
\* and at most one writer.
\* ----------------------------------------------------------------------
Safety ==
    /\ (writers = {} \/ readers = {})      \* readers and writers are never both non‑empty
    /\ Cardinality(writers) <= 1          \* at most one writer

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
RequestRead(p) ==
    /\ p \in n
    /\ p \notin readers
    /\ p \notin writers
    /\ p \notin WaitingSet
    /\ queue' = Append(queue, [proc |-> p, type |-> "Read"])
    /\ UNCHANGED << readers, writers >>

RequestWrite(p) ==
    /\ p \in n
    /\ p \notin readers
    /\ p \notin writers
    /\ p \notin WaitingSet
    /\ queue' = Append(queue, [proc |-> p, type |-> "Write"])
    /\ UNCHANGED << readers, writers >>

Serve ==
    /\ queue # << >>
    /\ writers = {}                     \* no writer currently active
    /\ LET front == Head(queue) IN
          IF front.type = "Read" THEN
              /\ readers' = readers \cup {front.proc}
              /\ writers' = writers
              /\ queue'   = Tail(queue)
          ELSE
              /\ readers' = {}
              /\ writers' = {front.proc}
              /\ queue'   = Tail(queue)
    /\ UNCHANGED readers \cup writers \ {front.proc}  \* other variables unchanged

Stop(p) ==
    /\ p \in readers \/ p \in writers
    /\ IF p \in readers THEN
          /\ readers' = readers \ {p}
          /\ writers' = writers
       ELSE
          /\ writers' = {}
          /\ readers' = readers
    /\ UNCHANGED queue

\* ----------------------------------------------------------------------
\* Composite actions for fairness
\* ----------------------------------------------------------------------
RequestReadAll == \E p \in n: RequestRead(p)
RequestWriteAll == \E p \in n: RequestWrite(p)
StopAll == \E p \in n: Stop(p)

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ RequestReadAll
    \/ RequestWriteAll
    \/ Serve
    \/ StopAll

\* ----------------------------------------------------------------------
\* Specification (including weak fairness for all actions)
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars
      /\ WF_vars(RequestReadAll)
      /\ WF_vars(RequestWriteAll)
      /\ WF_vars(Serve)
      /\ WF_vars(StopAll)

\* ----------------------------------------------------------------------
\* Liveness property: every process eventually reads, eventually writes,
\* and any active reader/writer eventually stops.
\* ----------------------------------------------------------------------
Liveness ==
    \A p \in n:
        (<> (p \in readers)                         \* eventually reads
         /\ <> (p \in writers)                     \* eventually writes
         /\ [] (p \in readers => <> (p \notin readers))  \* eventually stops reading
         /\ [] (p \in writers => <> (p \notin writers))) \* eventually stops writing

====