---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANT NumActors
Actors == 1..NumActors

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Request == [type : {"read", "write"}, proc : Actors]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES readers, writers, queue

\* ----------------------------------------------------------------------
\* Type invariant (helps TLC)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ readers \in SUBSET Actors
    /\ writers \in SUBSET Actors
    /\ queue \in Seq(Request)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = <<>>

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
RequestRead(p) ==
    /\ p \in Actors
    /\ ~(\E i \in 1..Len(queue) : queue[i].proc = p /\ queue[i].type = "read")
    /\ queue' = Append(queue, [type |-> "read", proc |-> p])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
    /\ p \in Actors
    /\ ~(\E i \in 1..Len(queue) : queue[i].proc = p /\ queue[i].type = "write")
    /\ queue' = Append(queue, [type |-> "write", proc |-> p])
    /\ UNCHANGED <<readers, writers>>

StartFromQueue ==
    /\ Len(queue) > 0
    /\ \A i \in 1..Len(queue) : ~(
            (queue[i].type = "write") /\ \E j \in 1..i-1 : queue[j].type = "read")
    /\ LET front == queue[1] IN
       IF front.type = "read" THEN
         /\ writers = {}               \* no writer may be active
         /\ readers' = readers \cup {front.proc}
         /\ writers' = writers
         /\ queue' = Tail(queue)
       ELSE  \* front.type = "write"
         /\ readers = {}               \* no reader may be active
         /\ writers' = {front.proc}
         /\ readers' = readers
         /\ queue' = Tail(queue)

StopRead(p) ==
    /\ p \in readers
    /\ readers' = readers \ {p}
    /\ UNCHANGED <<writers, queue>>

StopWrite(p) ==
    /\ p \in writers
    /\ writers' = {}
    /\ UNCHANGED <<readers, queue>>

Next ==
    \/ \E p \in Actors : RequestRead(p)
    \/ \E p \in Actors : RequestWrite(p)
    \/ StartFromQueue
    \/ \E p \in Actors : StopRead(p)
    \/ \E p \in Actors : StopWrite(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<readers, writers, queue>>

\* ----------------------------------------------------------------------
\* Safety invariant (derived from description)
\* ----------------------------------------------------------------------
Safety ==
    /\ (writers = {} => TRUE)     \* placeholder, actual condition below
    /\ (writers = {} => readers # {})
    /\ (readers = {} => TRUE)     \* placeholder
    /\ (Card(writers) <= 1)
    /\ ~(writers # {} /\ readers # {})

\* ----------------------------------------------------------------------
\* Liveness property (fairness is enforced in the .cfg, but we also expose it)
\* ----------------------------------------------------------------------
Liveness ==
    \A p \in Actors :
        <> (p \in readers) /\ <> (p \in writers)

\* ----------------------------------------------------------------------
\* Theorems (optional, but they expose the invariants)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Safety

====