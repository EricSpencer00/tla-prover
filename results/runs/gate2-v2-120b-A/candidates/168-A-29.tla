---- MODULE ReadersWriters ----
EXTENDS Sequences, FiniteSets, TLC

CONSTANT NumActors

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Proc == 1..NumActors
State == {"idle", "waiting", "reading", "writing"}

Req == [type : {"read", "write"}, proc : Proc]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLE readers, writers, queue

\* readers  : set of processes currently reading
\* writers  : set of processes currently writing (at most one)
\* queue    : sequence (ordered) of pending requests

\* ----------------------------------------------------------------------
\* Type correctness (helps TLC)
\* ----------------------------------------------------------------------
TypeOK == 
    /\ readers \in SUBSET Proc
    /\ writers \in SUBSET Proc
    /\ queue \in Seq(Req)

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
    /\ p \in Proc
    /\ ~(\E i \in 1..Len(queue) : queue[i].proc = p /\ queue[i].type = "read")
    /\ queue' = Append(queue, [type |-> "read", proc |-> p])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
    /\ p \in Proc
    /\ ~(\E i \in 1..Len(queue) : queue[i].proc = p /\ queue[i].type = "write")
    /\ queue' = Append(queue, [type |-> "write", proc |-> p])
    /\ UNCHANGED <<readers, writers>>

BeginOp ==
    /\ Len(queue) > 0
    /\ LET front == queue[1] IN
       IF front.type = "read" THEN
          /\ writers = {}               \* no writer active
          /\ readers' = readers \cup {front.proc}
          /\ writers' = {}
          /\ queue'   = Tail(queue)
       ELSE
          /\ front.type = "write"
          /\ readers = {}               \* no readers active
          /\ writers' = {front.proc}
          /\ readers' = {}
          /\ queue'   = Tail(queue)

Stop(p) ==
    /\ p \in Proc
    /\ readers' = readers \ {p}
    /\ writers' = writers \ {p}
    /\ UNCHANGED queue

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : RequestRead(p)
    \/ \E p \in Proc : RequestWrite(p)
    \/ BeginOp
    \/ \E p \in Proc : Stop(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<readers, writers, queue>>

\* ----------------------------------------------------------------------
\* Safety invariant (the required "Safety")
\* ----------------------------------------------------------------------
Safety ==
    /\ (writers = {} => readers # {})
       \/ (writers # {} => readers = {})
    /\ Cardinality(writers) <= 1

\* The model checker will also check TypeOK as an invariant.
=============================================================================