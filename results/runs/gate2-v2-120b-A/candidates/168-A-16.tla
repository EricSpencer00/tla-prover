---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\* Types and derived constants
\* ----------------------------------------------------------------------
Proc == 1..NumActors

REQTYPE == {"Read", "Write"}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Readers, Writers, Queue

\* ----------------------------------------------------------------------
\* State variables are: 
\*   Readers : subset of Proc   (processes currently reading)
\*   Writers : subset of Proc   (processes currently writing, at most one)
\*   Queue   : sequence of [pid : Proc, type : REQTYPE] 
\* ----------------------------------------------------------------------
vars == << Readers, Writers, Queue >>

\* ----------------------------------------------------------------------
\* Type invariant (helps TLC)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Readers \in SUBSET Proc
    /\ Writers \in SUBSET Proc
    /\ Queue   \in Seq([pid : Proc, type : REQTYPE])

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = << >>

\* ----------------------------------------------------------------------
\* Helper: request at the head of the queue, if any
\* ----------------------------------------------------------------------
HeadReq == IF Len(Queue) = 0 THEN [pid |-> 0, type |-> "Read"] ELSE Queue[1]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
RequestRead(pid) ==
    /\ pid \in Proc
    /\ ~(\E i \in 1..Len(Queue) : Queue[i].pid = pid /\ Queue[i].type = "Read")
    /\ Queue' = Queue \o <<[pid |-> pid, type |-> "Read"]>>
    /\ UNCHANGED <<Readers, Writers>>

RequestWrite(pid) ==
    /\ pid \in Proc
    /\ ~(\E i \in 1..Len(Queue) : Queue[i].pid = pid /\ Queue[i].type = "Write")
    /\ Queue' = Queue \o <<[pid |-> pid, type |-> "Write"]>>
    /\ UNCHANGED <<Readers, Writers>>

BeginAccess ==
    /\ Len(Queue) > 0
    /\ Writers = {}                     \* no writer active
    /\ IF HeadReq.type = "Read"
          THEN /\ Readers' = Readers \cup {HeadReq.pid}
               /\ Writers' = {}
               /\ Queue'   = Tail(Queue)
          ELSE /\ Writers = {}           \* ensure no writer yet
               /\ Readers = {}           \* ensure no reader for a write
               /\ Writers' = {HeadReq.pid}
               /\ Readers' = {}
               /\ Queue'   = Tail(Queue)

StopActivity(pid) ==
    /\ pid \in Proc
    /\ \/ pid \in Readers
       \/ pid \in Writers
    /\ Readers' = Readers \ {pid}
    /\ Writers' = Writers \ {pid}
    /\ UNCHANGED Queue

\* ----------------------------------------------------------------------
\* Stuttering step (allows the system to stay idle)
\* ----------------------------------------------------------------------
Idle ==
    UNCHANGED vars

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E pid \in Proc : RequestRead(pid)
    \/ \E pid \in Proc : RequestWrite(pid)
    \/ BeginAccess
    \/ \E pid \in Proc : StopActivity(pid)
    \/ Idle

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Safety invariant: never both readers and writers,
\* and at most one writer.
\* ----------------------------------------------------------------------
Safety ==
    /\ (Writers = {} => TRUE)               \* trivially true
    /\ (Readers = {} \/ Writers = {})       \* they cannot coexist
    /\ Cardinality(Writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness property placeholder (the .cfg will give a temporal formula)
\* ----------------------------------------------------------------------
Liveness == TRUE

====