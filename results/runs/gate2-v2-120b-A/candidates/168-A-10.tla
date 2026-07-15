---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANT NumActors

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Actors == 1 .. NumActors

\* Request type
ReadReq  == "Read"
WriteReq == "Write"
ReqTypes == {ReadReq, WriteReq}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES readers, writers, queue

\* ----------------------------------------------------------------------
\* Types (for TypeOK)
\* ----------------------------------------------------------------------
ReaderSet == SUBSET Actors
WriterSet == SUBSET Actors
Request   == [type : ReqTypes, proc : Actors]
QueueSeq  == Seq(Request)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = <<>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
IsRead(req)  == req.type = ReadReq
IsWrite(req) == req.type = WriteReq

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
RequestRead(p) ==
    /\ p \in Actors
    /\ p \notin { q.proc : q \in queue }
    /\ p \notin readers
    /\ p \notin writers
    /\ queue' = Append(queue, [type |-> ReadReq, proc |-> p])
    /\ readers' = readers
    /\ writers' = writers

RequestWrite(p) ==
    /\ p \in Actors
    /\ p \notin { q.proc : q \in queue }
    /\ p \notin readers
    /\ p \notin writers
    /\ queue' = Append(queue, [type |-> WriteReq, proc |-> p])
    /\ readers' = readers
    /\ writers' = writers

BeginFront() ==
    /\ Len(queue) > 0
    /\ LET front == queue[1] IN
       /\ writers = {}          \* no active writer
       /\ IF front.type = ReadReq THEN
            /\ readers' = readers \cup {front.proc}
            /\ writers' = writers
            /\ queue'   = Tail(queue)
          ELSE
            /\ front.type = WriteReq
            /\ readers = {}      \* no active readers
            /\ writers' = {front.proc}
            /\ readers' = {}
            /\ queue'   = Tail(queue)

StopReading(p) ==
    /\ p \in readers
    /\ readers' = readers \ {p}
    /\ writers' = writers
    /\ queue'   = queue

StopWriting(p) ==
    /\ p \in writers
    /\ writers' = {}
    /\ readers' = readers
    /\ queue'   = queue

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Actors: RequestRead(p)
    \/ \E p \in Actors: RequestWrite(p)
    \/ BeginFront()
    \/ \E p \in Actors: StopReading(p)
    \/ \E p \in Actors: StopWriting(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<readers, writers, queue>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ readers \in ReaderSet
    /\ writers \in WriterSet
    /\ readers # {} => writers = {}
    /\ writers # {} => readers = {}
    /\ queue \in QueueSeq
    /\ \A i \in DOMAIN queue: queue[i] \in Request

\* ----------------------------------------------------------------------
\* Safety invariant (mutual exclusion and at most one writer)
\* ----------------------------------------------------------------------
Safety ==
    /\ readers = {} \/ writers = {}
    /\ Cardinality(writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness property: every process eventually reads and eventually writes
\* ----------------------------------------------------------------------
Liveness ==
    /\ \A p \in Actors: <> (p \in readers)
    /\ \A p \in Actors: <> (p \in writers)

====