---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Actor == 1..NumActors
ReqType == {"Read", "Write"}
Request == [type : ReqType, proc : Actor]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES readers, writers, queue

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ActiveSet == readers \cup writers

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
    /\ p \in Actor
    /\ \A q \in queue: q.proc # p
    /\ queue' = Append(queue, [type |-> "Read", proc |-> p])
    /\ UNCHANGED << readers, writers >>

RequestWrite(p) ==
    /\ p \in Actor
    /\ \A q \in queue: q.proc # p
    /\ queue' = Append(queue, [type |-> "Write", proc |-> p])
    /\ UNCHANGED << readers, writers >>

BeginProcessing ==
    /\ queue # << >>
    /\ writers = {}               \* no writer currently active
    /\ LET front == Head(queue) IN
       IF front.type = "Read" THEN
          /\ readers' = readers \cup {front.proc}
          /\ writers' = writers
          /\ queue'   = Tail(queue)
       ELSE
          /\ readers = {}          \* no readers must be active for a write
          /\ writers' = {front.proc}
          /\ readers' = {}
          /\ queue'   = Tail(queue)

StopActivity(p) ==
    /\ p \in Actor
    /\ \/ p \in readers
       \/ p \in writers
    /\ readers' = readers \ {p}
    /\ writers' = writers \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in Actor: RequestRead(p)
    \/ \E p \in Actor: RequestWrite(p)
    \/ BeginProcessing
    \/ \E p \in Actor: StopActivity(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<readers, writers, queue>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ readers \subseteq Actor
    /\ writers \subseteq Actor
    /\ writers \subseteq {w \in Actor : w \notin readers}
    /\ \A i \in 1..Len(queue):
          /\ queue[i].type \in ReqType
          /\ queue[i].proc \in Actor

\* ----------------------------------------------------------------------
\* Safety invariant (the required Safety)
\* ----------------------------------------------------------------------
Safety ==
    /\ (writers = {} \/ readers = {})
    /\ Cardinality(writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness property (the required Liveness)
\* ----------------------------------------------------------------------
Liveness == 
    /\ \A p \in Actor: <> (p \in readers)   \* every process eventually reads
    /\ \A p \in Actor: <> (p \in writers)   \* every process eventually writes

====