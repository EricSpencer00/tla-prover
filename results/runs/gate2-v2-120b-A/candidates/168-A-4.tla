---- MODULE ReadersWriters ----
EXTENDS FiniteSets, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANT NumActors

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Actors == 1 .. NumActors

\* Request types
\* ----------------------------------------------------------------------
ReadReq  == "Read"
WriteReq == "Write"
ReqTypes == {ReadReq, WriteReq}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES readers, writers, queue

\* readers  : set of processes currently reading
\* writers  : set of processes currently writing (must be empty or singleton)
\* queue    : sequence of [proc: Actors, type: ReqTypes] representing pending requests
\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
EmptyQueue == << >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = EmptyQueue

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* (1) Request to read
RequestRead(p) ==
    /\ p \in Actors
    /\ ~(\E i \in 1..Len(queue): queue[i].proc = p /\ queue[i].type = ReadReq)
    /\ queue' = Append(queue, [proc |-> p, type |-> ReadReq])
    /\ UNCHANGED <<readers, writers>>

\* (2) Request to write
RequestWrite(p) ==
    /\ p \in Actors
    /\ ~(\E i \in 1..Len(queue): queue[i].proc = p /\ queue[i].type = WriteReq)
    /\ queue' = Append(queue, [proc |-> p, type |-> WriteReq])
    /\ UNCHANGED <<readers, writers>>

\* (3) Begin reading or writing
ProcessQueue ==
    /\ Len(queue) > 0
    /\ ~writers
    /\ LET front == queue[1] IN
       IF front.type = ReadReq THEN
          /\ readers' = readers \cup {front.proc}
          /\ writers' = writers
          /\ queue'   = Tail(queue)
       ELSE (* WriteReq *)
          /\ ~readers
          /\ writers' = {front.proc}
          /\ readers' = {}
          /\ queue'   = Tail(queue)

\* (4) Stop reading
StopReading(p) ==
    /\ p \in readers
    /\ readers' = readers \ {p}
    /\ UNCHANGED <<writers, queue>>

\* (5) Stop writing
StopWriting(p) ==
    /\ p \in writers
    /\ writers' = {}
    /\ UNCHANGED <<readers, queue>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
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
\* Type correctness invariant (optional but useful)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ writers \subseteq {1} \/ writers = {}
    /\ \A i \in 1..Len(queue): 
         /\ queue[i].proc \in Actors
         /\ queue[i].type \in ReqTypes

\* ----------------------------------------------------------------------
\* Safety invariant (as described)
\* ----------------------------------------------------------------------
Safety ==
    /\ ~(readers # {} /\ writers # {})
    /\ Cardinality(writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness property (placeholder, actual property defined in .cfg)
\* ----------------------------------------------------------------------
Liveness == TRUE

====