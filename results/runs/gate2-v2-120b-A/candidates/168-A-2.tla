---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Actors == 1..NumActors

Request == [type : {"read", "write"}, pid : Actors]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES readers, writers, queue

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Readers == readers
Writers == writers
Queue   == queue

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
RequestRead(pid) ==
    /\ pid \in Actors
    /\ pid \notin { r.pid : r \in queue \* but only if already queued } 
       \* Ensure the process is not already waiting (any request)
    /\ queue' = Append(queue, [type |-> "read", pid |-> pid])
    /\ UNCHANGED << readers, writers >>

RequestWrite(pid) ==
    /\ pid \in Actors
    /\ pid \notin { r.pid : r \in queue }
    /\ queue' = Append(queue, [type |-> "write", pid |-> pid])
    /\ UNCHANGED << readers, writers >>

BeginAccess ==
    /\ Len(queue) > 0
    /\ writers = {}               \* no writer currently active
    /\ LET front == Head(queue) IN
          IF front.type = "read" THEN
              /\ readers' = readers \cup {front.pid}
              /\ writers' = {}
              /\ queue'   = Tail(queue)
          ELSE            \* write request
              /\ readers = {}        \* no readers active
              /\ writers' = {front.pid}
              /\ queue'   = Tail(queue)
    /\ UNCHANGED readers   \* for the write branch readers is unchanged but already = {}
    /\ UNCHANGED writers   \* for the read branch writers unchanged but already = {}

Stop(pid) ==
    /\ pid \in Actors
    /\ \/ pid \in readers
       \/ pid \in writers
    /\ readers' = readers \ {pid}
    /\ writers' = writers \ {pid}
    /\ UNCHANGED queue

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E pid \in Actors: RequestRead(pid)
    \/ \E pid \in Actors: RequestWrite(pid)
    \/ BeginAccess
    \/ \E pid \in Actors: Stop(pid)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<readers, writers, queue>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ /\ writers = {} \/ \E pid \in Actors: writers = {pid}
       /\ /\ readers = {} \/ \A pid \in readers: pid \in Actors
    /\ queue \in Seq(Request)
    /\ \A i \in 1..Len(queue):
          /\ queue[i].type \in {"read", "write"}
          /\ queue[i].pid \in Actors

\* ----------------------------------------------------------------------
\* Safety invariant (the one required)
\* ----------------------------------------------------------------------
Safety ==
    /\ \/ writers = {}               \* no writer, any number of readers allowed
       \/ readers = {}               \* no readers, at most one writer (ensured by TypeOK)
    /\ Cardinality(writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness property (the one required)
\* ----------------------------------------------------------------------
Liveness ==
    /\ \A pid \in Actors: <> (pid \in Readers)
    /\ \A pid \in Actors: <> (pid \in Writers)

====