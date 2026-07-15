---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANT NumActors

\* The set of all process identifiers
ProcSet == 1..NumActors

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Request == [type : {"read", "write"}, proc : ProcSet]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Readers, Writers, Queue

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
IsIdle(p) == p \notin Readers /\ p \notin Writers /\ ~(\E i \in 1..Len(Queue) : Queue[i].proc = p)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = <<>>

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
RequestRead(p) ==
    /\ p \in ProcSet
    /\ IsIdle(p)               \* not already waiting or active
    /\ Queue' = Queue \o <<[type |-> "read", proc |-> p]>>
    /\ UNCHANGED <<Readers, Writers>>

RequestWrite(p) ==
    /\ p \in ProcSet
    /\ IsIdle(p)
    /\ Queue' = Queue \o <<[type |-> "write", proc |-> p]>>
    /\ UNCHANGED <<Readers, Writers>>

BeginOp ==
    /\ Queue # <<>>
    /\ LET front == Queue[1] IN
       IF front.type = "read" THEN
          /\ Writers = {}               \* no writer active
          /\ Readers' = Readers \cup {front.proc}
          /\ Writers' = Writers
          /\ Queue'   = Tail(Queue)
       ELSE
          /\ front.type = "write"
          /\ Readers = {}               \* no readers active
          /\ Writers' = Writers \cup {front.proc}
          /\ Readers' = Readers
          /\ Queue'   = Tail(Queue)

Stop(p) ==
    /\ p \in Readers \/ p \in Writers
    /\ IF p \in Readers
          THEN Readers' = Readers \ {p}
          ELSE UNCHANGED Readers
    /\ IF p \in Writers
          THEN Writers' = Writers \ {p}
          ELSE UNCHANGED Writers
    /\ UNCHANGED Queue

Next ==
    \/ \E p \in ProcSet : RequestRead(p)
    \/ \E p \in ProcSet : RequestWrite(p)
    \/ BeginOp
    \/ \E p \in ProcSet : Stop(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Readers, Writers, Queue>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Readers \subseteq ProcSet
    /\ Writers \subseteq ProcSet
    /\ Disjoint(Readers, Writers)
    /\ \A i \in 1..Len(Queue) : Queue[i] \in Request

\* ----------------------------------------------------------------------
\* Safety invariant (the required safety property)
\* ----------------------------------------------------------------------
Safety ==
    /\ ~(Readers # {} /\ Writers # {})   \* never both non‑empty
    /\ Cardinality(Writers) <= 1          \* at most one writer

\* ----------------------------------------------------------------------
\* Liveness property (the required liveness)
\* ----------------------------------------------------------------------
Liveness ==
    /\ \A p \in ProcSet : <>[](p \in Readers \/ p \in Writers => <> (p \notin Readers /\ p \notin Writers))
    /\ \A p \in ProcSet : <>[](p \notin Readers /\ p \notin Writers => <> (p \in Readers \/ p \in Writers))

====