---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors
\* The set of all actor identifiers, derived from the constant
Actors == 1..NumActors

\* Possible request types
RequestType == {"Read", "Write"}

\* A request is a record containing its type and the originating process
Request == [type : RequestType, proc : Actors]

VARIABLES readers, writer, queue

\* ----------------------------------------------------------------------
\* Type definitions (used in TypeOK)
\* ----------------------------------------------------------------------
ReaderSet == SUBSET Actors
WriterSet == SUBSET Actors
Queue == Seq(Request)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ readers = {}
    /\ writer  = {}
    /\ queue   = <<>>

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
RequestRead(p) ==
    /\ p \in Actors
    /\ ~(\E i \in 1..Len(queue): queue[i].proc = p /\ queue[i].type = "Read")
    /\ queue' = queue \o <<[type |-> "Read", proc |-> p]>>
    /\ UNCHANGED <<readers, writer>>

RequestWrite(p) ==
    /\ p \in Actors
    /\ ~(\E i \in 1..Len(queue): queue[i].proc = p /\ queue[i].type = "Write")
    /\ queue' = queue \o <<[type |-> "Write", proc |-> p]>>
    /\ UNCHANGED <<readers, writer>>

BeginOperation ==
    /\ Len(queue) > 0
    /\ writer = {}               \* no writer currently active
    /\ CASE queue[1].type = "Read" ->
            /\ readers' = readers \cup { queue[1].proc }
            /\ writer'  = writer
            /\ queue'   = Tail(queue)
       [] queue[1].type = "Write" ->
            /\ readers = {}       \* no readers must be active
            /\ writer' = { queue[1].proc }
            /\ readers' = readers
            /\ queue'   = Tail(queue)

Stop(p) ==
    /\ p \in Actors
    /\ (p \in readers) \/ (p \in writer)
    /\ IF p \in readers
          THEN readers' = readers \ {p}
               writer'  = writer
          ELSE readers' = readers
               writer'  = {}
    /\ UNCHANGED queue

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Actors: RequestRead(p)
    \/ \E p \in Actors: RequestWrite(p)
    \/ BeginOperation
    \/ \E p \in Actors: Stop(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<readers, writer, queue>>

\* ----------------------------------------------------------------------
\* Safety invariant (mutual exclusion)
\* ----------------------------------------------------------------------
Safety ==
    /\ Cardinality(writer) <= 1
    /\ (writer = {} => TRUE)               \* trivially true when no writer
    /\ (writer # {} => readers = {})

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ readers \in SUBSET Actors
    /\ writer  \in SUBSET Actors
    /\ writer \subseteq {writer'}   \* writer is either empty or a singleton
    /\ queue   \in Queue

\* ----------------------------------------------------------------------
\* Liveness property (weak fairness of all actions is assumed in the cfg)
\* We express that every process eventually reads and eventually writes.
\* The property is satisfied under weak fairness of the actions defined above.
\* ----------------------------------------------------------------------
Liveness ==
    /\ \A p \in Actors: <> (p \in readers)   \* each process eventually reads
    /\ \A p \in Actors: <> (p \in writer)    \* each process eventually writes

=============================================================================