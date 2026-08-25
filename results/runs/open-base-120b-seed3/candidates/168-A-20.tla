---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\* Convenience definition for the set of actor identifiers
\* (the .cfg file will substitute a concrete value for NumActors)
\* ----------------------------------------------------------------------
n == 1 .. NumActors

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES Readers, Writers, Queue

\* ----------------------------------------------------------------------
\* Type of a request in the waiting queue
\* ----------------------------------------------------------------------
Req == [proc : n, type : {"read", "write"}]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = << >>

\* ----------------------------------------------------------------------
\* Action: a process requests read access
\* ----------------------------------------------------------------------
RequestRead(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ \A q \in DOMAIN Queue :
          ~(Queue[q].proc = p /\ Queue[q].type = "read")
    /\ Queue' = Append(Queue, [proc |-> p, type |-> "read"])
    /\ UNCHANGED << Readers, Writers >>

\* ----------------------------------------------------------------------
\* Action: a process requests write access
\* ----------------------------------------------------------------------
RequestWrite(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ \A q \in DOMAIN Queue :
          ~(Queue[q].proc = p /\ Queue[q].type = "write")
    /\ Queue' = Append(Queue, [proc |-> p, type |-> "write"])
    /\ UNCHANGED << Readers, Writers >>

\* ----------------------------------------------------------------------
\* Action: the front request of the queue is processed
\* ----------------------------------------------------------------------
ProcessQueue ==
    /\ Queue # << >>
    /\ Writers = {}               \* no writer currently active
    /\ LET front == Head(Queue) IN
          /\ CASE front.type = "read" ->
                 /\ Readers' = Readers \cup {front.proc}
                 /\ Writers' = Writers
                 /\ Queue'   = Tail(Queue)
             [] front.type = "write" ->
                 /\ Readers = {}                 \* no readers active
                 /\ Writers' = Writers \cup {front.proc}
                 /\ Readers' = Readers
                 /\ Queue'   = Tail(Queue)
          \* No other type possible
    /\ UNCHANGED << >>   \* (Readers', Writers', Queue' already defined)

\* ----------------------------------------------------------------------
\* Action: a process stops its current activity
\* ----------------------------------------------------------------------
Stop(p) ==
    /\ p \in n
    /\ \/ p \in Readers
       \/ p \in Writers
    /\ IF p \in Readers THEN
          /\ Readers' = Readers \ {p}
          /\ Writers' = Writers
       ELSE
          /\ Writers' = Writers \ {p}
          /\ Readers' = Readers
    /\ UNCHANGED Queue

\* ----------------------------------------------------------------------
\* Composite next-state relation
\* ----------------------------------------------------------------------
RequestReadAction == \E p \in n : RequestRead(p)
RequestWriteAction == \E p \in n : RequestWrite(p)
StopAction == \E p \in n : Stop(p)

Next ==
    \/ RequestReadAction
    \/ RequestWriteAction
    \/ ProcessQueue
    \/ StopAction

\* ----------------------------------------------------------------------
\* Specification (includes weak fairness for all actions)
\* ----------------------------------------------------------------------
Spec ==
    Init /\
    [][Next]_<<Readers, Writers, Queue>> /\
    WF_<<Readers, Writers, Queue>>(RequestReadAction) /\
    WF_<<Readers, Writers, Queue>>(RequestWriteAction) /\
    WF_<<Readers, Writers, Queue>>(ProcessQueue) /\
    WF_<<Readers, Writers, Queue>>(StopAction)

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Readers \cap Writers = {}
    /\ Queue \in Seq(Req)

\* ----------------------------------------------------------------------
\* Safety invariant (no simultaneous readers & writers, at most one writer)
\* ----------------------------------------------------------------------
Safety ==
    /\ (Readers = {} \/ Writers = {})
    /\ Cardinality(Writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness property
\*   - every process eventually reads and eventually writes
\*   - any active reader eventually stops
\*   - any active writer eventually stops
\* ----------------------------------------------------------------------
Liveness ==
    \A p \in n :
        /\ <> (p \in Readers)            \* p eventually reads
        /\ <> (p \in Writers)            \* p eventually writes
        /\ [] (p \in Readers => <> (p \notin Readers))   \* readers stop
        /\ [] (p \in Writers => <> (p \notin Writers))   \* writers stop

====