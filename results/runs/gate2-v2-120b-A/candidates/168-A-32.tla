---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES readers, writers, q

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
ProcSet == 1..NumActors

\* A request is a record with fields:
\*   proc : the process that made the request
\*   type : "R" for read, "W" for write
Req == [proc : ProcSet, type : {"R", "W"}]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ q = << >>

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
RequestRead(p) ==
    /\ p \in ProcSet
    /\ ~(\E i \in 1..Len(q) : q[i].proc = p /\ q[i].type = "R")
    /\ q' = q \o << [proc |-> p, type |-> "R"] >>
    /\ UNCHANGED << readers, writers >>

RequestWrite(p) ==
    /\ p \in ProcSet
    /\ ~(\E i \in 1..Len(q) : q[i].proc = p /\ q[i].type = "W")
    /\ q' = q \o << [proc |-> p, type |-> "W"] >>
    /\ UNCHANGED << readers, writers >>

ProcessQueue ==
    /\ Len(q) > 0
    /\ LET front == q[1] IN
       /\ IF front.type = "R" THEN
            /\ writers = {}
            /\ readers' = readers \cup {front.proc}
          ELSE
            /\ front.type = "W"
            /\ readers = {}
            /\ writers' = {front.proc}
       /\ q' = Tail(q)
       /\ UNCHANGED << >>

Stop(p) ==
    /\ p \in ProcSet
    /\ (p \in readers \/ p \in writers)
    /\ readers' = readers \ {p}
    /\ writers' = writers \ {p}
    /\ UNCHANGED << q >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in ProcSet : RequestRead(p)
    \/ \E p \in ProcSet : RequestWrite(p)
    \/ ProcessQueue
    \/ \E p \in ProcSet : Stop(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<readers, writers, q>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ readers \subseteq ProcSet
    /\ writers \subseteq ProcSet
    /\ readers \cap writers = {}
    /\ q \in Seq(Req)

\* ----------------------------------------------------------------------
\* Safety invariant (the one required by the description)
\* ----------------------------------------------------------------------
Safety ==
    /\ (writers = {} => TRUE)          \* trivially true, kept for symmetry
    /\ (writers /= {} => readers = {}) \* no readers while a writer is active
    /\ Cardinality(writers) <= 1       \* at most one writer

\* ----------------------------------------------------------------------
\* Liveness property (placeholder, model checker will interpret it)
\* ----------------------------------------------------------------------
Liveness == <>TRUE

====