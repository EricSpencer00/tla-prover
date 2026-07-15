---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\* Basic definitions
\* ----------------------------------------------------------------------
Actors == 1 .. NumActors

RequestType == {"Read", "Write"}

\* A request is a record containing the requester and the desired operation.
Request == [proc : 1..NumActors, op : RequestType]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES readers, writers, queue

\* readers  : set of processes currently reading
\* writers  : set of processes currently writing (will contain at most one)
\* queue    : ordered sequence of pending requests

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* No process can be both a reader and a writer.
DisjointReadersWriters == readers \cap writers = {}

\* At most one writer.
AtMostOneWriter == Cardinality(writers) <= 1

\* Type correctness predicate (used for the TypeOK invariant).
TypeOK ==
    /\ readers \in SUBSET Actors
    /\ writers \in SUBSET Actors
    /\ queue \in Seq(Request)
    /\ \A i \in DOMAIN queue: queue[i] \in Request

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
\* (1) A process that is not already waiting to read joins the queue with a read request.
RequestRead(p) ==
    /\ p \in Actors
    /\ ~(\E i \in DOMAIN queue: queue[i].proc = p /\ queue[i].op = "Read")
    /\ queue' = Append(queue, [proc |-> p, op |-> "Read"])
    /\ UNCHANGED <<readers, writers>>

\* (2) A process that is not already waiting to write joins the queue with a write request.
RequestWrite(p) ==
    /\ p \in Actors
    /\ ~(\E i \in DOMAIN queue: queue[i].proc = p /\ queue[i].op = "Write")
    /\ queue' = Append(queue, [proc |-> p, op |-> "Write"])
    /\ UNCHANGED <<readers, writers>>

\* (3) Process the head of the queue if possible.
ProcessQueue ==
    /\ Len(queue) > 0
    /\ IF queue[1].op = "Read" THEN
          /\ writers = {}               \* no writer active
          /\ readers' = readers \cup {queue[1].proc}
       ELSE
          /\ queue[1].op = "Write"
          /\ writers = {}               \* no writer yet
          /\ readers = {}               \* no readers active
          /\ writers' = {queue[1].proc}
    /\ queue' = Tail(queue)
    /\ UNCHANGED <<readers, writers>> \* for the branch that does not modify

\* (4) Any active reader may stop.
StopReading(p) ==
    /\ p \in readers
    /\ readers' = readers \ {p}
    /\ UNCHANGED <<writers, queue>>

\* (5) Any active writer may stop.
StopWriting(p) ==
    /\ p \in writers
    /\ writers' = {}
    /\ UNCHANGED <<readers, queue>>

\* Union of all possible next steps.
Next ==
    \/ \E p \in Actors: RequestRead(p)
    \/ \E p \in Actors: RequestWrite(p)
    \/ ProcessQueue
    \/ \E p \in Actors: StopReading(p)
    \/ \E p \in Actors: StopWriting(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<readers, writers, queue>>

\* ----------------------------------------------------------------------
\* Safety invariant (the one described in the natural language)
\* ----------------------------------------------------------------------
Safety == /\ DisjointReadersWriters
          /\ AtMostOneWriter

\* ----------------------------------------------------------------------
\* Liveness property (informal: every process eventually reads and writes)
\* ----------------------------------------------------------------------
Liveness == 
    /\ \A p \in Actors: <> (p \in readers)   \* eventually p reads
    /\ \A p \in Actors: <> (p \in writers)   \* eventually p writes

\* ----------------------------------------------------------------------
\* THEOREMS (optional, just to expose the identifiers)
\* ----------------------------------------------------------------------
THEOREM SpecImpliesSafety == Spec => []Safety

====