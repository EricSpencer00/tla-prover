---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, TLC

CONSTANT NumActors

\* The set of process identifiers (overridden by the cfg substitution)
n == 1 .. NumActors
Proc == n

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES Readers, Writers, Queue

vars == << Readers, Writers, Queue >>

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Request == [proc : Proc, type : {"Read", "Write"}]

TypeOK ==
    /\ Readers \subseteq Proc
    /\ Writers \subseteq Proc
    /\ Readers \cap Writers = {}
    /\ Cardinality(Writers) <= 1
    /\ Queue \in Seq(Request)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue = << >>

\* ----------------------------------------------------------------------
\* Helper predicates
\* ----------------------------------------------------------------------
Waiting(p, t) ==
    \E r \in Queue : /\ r.proc = p
                     /\ r.type = t

Idle(p) ==
    /\ p \notin Readers
    /\ p \notin Writers
    /\ \A r \in Queue : r.proc # p

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
RequestRead(p) ==
    /\ Idle(p)
    /\ ~Waiting(p, "Read")
    /\ Queue' = Append(Queue, [proc |-> p, type |-> "Read"])
    /\ UNCHANGED << Readers, Writers >>

RequestWrite(p) ==
    /\ Idle(p)
    /\ ~Waiting(p, "Write")
    /\ Queue' = Append(Queue, [proc |-> p, type |-> "Write"])
    /\ UNCHANGED << Readers, Writers >>

BeginProcessing ==
    /\ Queue # << >>
    /\ Writers = {}               \* no writer currently active
    /\ LET front == Head(Queue) IN
       IF front.type = "Read" THEN
          /\ Readers' = Readers \cup {front.proc}
          /\ Writers' = Writers
          /\ Queue' = Tail(Queue)
       ELSE \* front.type = "Write"
          /\ Readers = {}                     \* no readers currently active
          /\ Writers' = Writers \cup {front.proc}
          /\ Readers' = Readers
          /\ Queue' = Tail(Queue)
    /\ UNCHANGED << >>

Stop(p) ==
    /\ p \in Readers \/ p \in Writers
    /\ IF p \in Readers THEN
          /\ Readers' = Readers \ {p}
          /\ Writers' = Writers
       ELSE
          /\ Writers' = Writers \ {p}
          /\ Readers' = Readers
    /\ UNCHANGED << Queue >>

\* The next-state relation is the disjunction of all possible actions
Next ==
    \/ \E p \in Proc : RequestRead(p)
    \/ \E p \in Proc : RequestWrite(p)
    \/ BeginProcessing
    \/ \E p \in Proc : Stop(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Safety invariant
\* ----------------------------------------------------------------------
Safety ==
    /\ (Readers = {} \/ Writers = {})
    /\ Cardinality(Writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Liveness ==
    \A p \in Proc :
        /\ <> (p \in Readers)               \* every process eventually reads
        /\ <> (p \in Writers)               \* every process eventually writes
        /\ [] (p \in Readers => <> (p \notin Readers))   \* readers eventually stop
        /\ [] (p \in Writers => <> (p \notin Writers))   \* writers eventually stop

\* ----------------------------------------------------------------------
\* THEOREMS (optional, for model checking)
\* ----------------------------------------------------------------------
THEOREM TypeOKInv == Spec => []TypeOK
THEOREM SafetyInv == Spec => []Safety

====