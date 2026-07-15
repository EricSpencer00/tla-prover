---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, TLC

CONSTANT NumActors

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Actor == 0..(NumActors - 1)

ActionType == {"Read", "Write"}

\* A request is a record containing the kind of action and the process that made it
Request == [type : ActionType, proc : Actor]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES readers, writers, queue

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of all possible requests that could appear in the queue
AllRequests == { [type |-> t, proc |-> p] : t \in ActionType, p \in Actor }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = <<>>

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
RequestRead(p) ==
    /\ p \in Actor
    /\ ~(\E i \in 1..Len(queue) : queue[i].proc = p /\ queue[i].type = "Read")
    /\ queue' = Append(queue, [type |-> "Read", proc |-> p])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
    /\ p \in Actor
    /\ ~(\E i \in 1..Len(queue) : queue[i].proc = p /\ queue[i].type = "Write")
    /\ queue' = Append(queue, [type |-> "Write", proc |-> p])
    /\ UNCHANGED <<readers, writers>>

BeginAccess ==
    /\ Len(queue) > 0
    /\ LET front == queue[1] IN
       /\ IF front.type = "Read" THEN
            /\ writers = {}
            /\ readers' = readers \cup {front.proc}
            /\ writers' = writers
          ELSE
            /\ front.type = "Write"
            /\ readers = {}
            /\ writers' = writers \cup {front.proc}
            /\ readers' = readers
       /\ queue' = Tail(queue)

Stop(p) ==
    /\ p \in readers \/ p \in writers
    /\ readers' = readers \ {p}
    /\ writers' = writers \ {p}
    /\ UNCHANGED queue

\* ----------------------------------------------------------------------
\* Next-state relation (allow any of the actions)
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Actor : RequestRead(p)
    \/ \E p \in Actor : RequestWrite(p)
    \/ BeginAccess
    \/ \E p \in Actor : Stop(p)

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
    /\ Disjoint(readers, writers)
    /\ /\ \A i \in 1..Len(queue) : queue[i] \in AllRequests
       /\ \A i, j \in 1..Len(queue) :
            (i # j) => (queue[i].proc # queue[j].proc)

\* ----------------------------------------------------------------------
\* Safety invariant (the two safety conditions stated in the description)
\* ----------------------------------------------------------------------
Safety ==
    /\ ~(\E w \in writers : \E r \in readers : TRUE)   \* no simultaneous reader and writer
    /\ Cardinality(writers) <= 1                        \* at most one writer

\* ----------------------------------------------------------------------
\* Liveness property (informal: every process eventually gets to read and write)
\* Note: This is a placeholder; the actual .cfg will refer to the concrete
\* temporal operators. Here we expose the atomic actions that the .cfg can
\* combine with fairness.
\* ----------------------------------------------------------------------
Liveness ==
    /\ \A p \in Actor : <> (p \in readers)   \* eventually p reads
    /\ \A p \in Actor : <> (p \in writers)   \* eventually p writes

====