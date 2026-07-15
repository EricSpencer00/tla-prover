---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* Set of all actor identifiers
Actors == 1..NumActors

\* Types of requests
ReqType == {"Read", "Write"}

\* A request records the type and the process that made it
Request == [type : ReqType, proc : Actors]

VARIABLES readers, writers, queue

\* ----------------------------------------------------------------------
\* Type invariant (helps TLC, also required as TypeOK)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ readers \in SUBSET Actors
    /\ writers \in SUBSET Actors
    /\ queue   \in Seq(Request)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = << >>

\* ----------------------------------------------------------------------
\* Helper to check that a process is not already waiting in the queue
\* ----------------------------------------------------------------------
NotWaiting(p) ==
    \A i \in 1..Len(queue) : queue[i].proc # p

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
RequestRead(p) ==
    /\ p \in Actors
    /\ p \notin readers
    /\ p \notin writers
    /\ NotWaiting(p)
    /\ queue' = Append(queue, [type |-> "Read", proc |-> p])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
    /\ p \in Actors
    /\ p \notin readers
    /\ p \notin writers
    /\ NotWaiting(p)
    /\ queue' = Append(queue, [type |-> "Write", proc |-> p])
    /\ UNCHANGED <<readers, writers>>

BeginAct ==
    /\ Len(queue) > 0
    /\ writers = {}               \* No writer active
    /\ IF queue[1].type = "Read" THEN
          /\ readers' = readers \cup { queue[1].proc }
          /\ writers' = writers
       ELSE
          /\ writers' = { queue[1].proc }
          /\ readers' = readers
    /\ queue' = Tail(queue)
    /\ UNCHANGED << >>

Stop(p) ==
    \/ /\ p \in readers
       /\ readers' = readers \ { p }
       /\ writers' = writers
    \/ /\ p \in writers
       /\ writers' = {}
       /\ readers' = readers
    /\ UNCHANGED queue

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Actors : RequestRead(p)
    \/ \E p \in Actors : RequestWrite(p)
    \/ BeginAct
    \/ \E p \in Actors : Stop(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<readers, writers, queue>>

\* ----------------------------------------------------------------------
\* Safety invariant (the required safety condition)
\* ----------------------------------------------------------------------
Safety ==
    /\ (writers = {} => TRUE)               \* trivial, keep structure
    /\ (writers # {} => readers = {})        \* no readers while writing
    /\ Cardinality(writers) <= 1             \* at most one writer

\* ----------------------------------------------------------------------
\* Liveness property: every process eventually reads and eventually writes
\* (combined as a single property for brevity)
\* ----------------------------------------------------------------------
Liveness ==
    \A p \in Actors : <> (p \in readers) /\ <> (p \in writers)

====