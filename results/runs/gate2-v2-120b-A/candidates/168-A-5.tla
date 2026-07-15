---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\* Sets and derived constants
\* ----------------------------------------------------------------------
Actors == 1..NumActors

ReadReq  == "Read"
WriteReq == "Write"
ReqType  == {ReadReq, WriteReq}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES readers, writers, queue

\* readers  : set of Actors currently reading
\* writers  : set of Actors currently writing (will be at most one)
\* queue    : sequence of requests, each a record [type : ReqType, proc : Actors]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Request(proc, rtype) == [type |-> rtype, proc |-> proc]

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
(\* Process p requests to read, provided it is not already waiting to read \*)
RequestRead(p) ==
    /\ p \in Actors
    /\ ~(\E i \in 1..Len(queue) : queue[i].proc = p /\ queue[i].type = ReadReq)
    /\ queue' = Append(queue, Request(p, ReadReq))
    /\ UNCHANGED <<readers, writers>>

(\* Process p requests to write, provided it is not already waiting to write \*)
RequestWrite(p) ==
    /\ p \in Actors
    /\ ~(\E i \in 1..Len(queue) : queue[i].proc = p /\ queue[i].type = WriteReq)
    /\ queue' = Append(queue, Request(p, WriteReq))
    /\ UNCHANGED <<readers, writers>>

(\* The front request is granted according to the rules described \*)
BeginActivity ==
    /\ Len(queue) > 0
    /\ LET front == queue[1] IN
       /\ IF front.type = ReadReq THEN
            /\ writers = {}               \* no writer active
            /\ readers' = readers \cup {front.proc}
            /\ writers' = writers
            /\ queue' = Tail(queue)
          ELSE
            /\ front.type = WriteReq
            /\ readers = {}               \* no readers active
            /\ writers' = {front.proc}
            /\ readers' = readers
            /\ queue' = Tail(queue)

(\* Any active reader may stop \*)
StopRead(p) ==
    /\ p \in readers
    /\ readers' = readers \ {p}
    /\ UNCHANGED <<writers, queue>>

(\* Any active writer may stop \*)
StopWrite(p) ==
    /\ p \in writers
    /\ writers' = {}
    /\ UNCHANGED <<readers, queue>>

Next ==
    \/ \E p \in Actors : RequestRead(p)
    \/ \E p \in Actors : RequestWrite(p)
    \/ BeginActivity
    \/ \E p \in Actors : StopRead(p)
    \/ \E p \in Actors : StopWrite(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<readers, writers, queue>>

\* ----------------------------------------------------------------------
\* Type correctness invariant (helps TLC, not the safety property)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ \A i \in 1..Len(queue) :
          /\ queue[i].type \in ReqType
          /\ queue[i].proc \in Actors

\* ----------------------------------------------------------------------
\* Safety invariant derived from the description
\* ----------------------------------------------------------------------
Safety ==
    /\ (writers = {} \/ readers = {})   \* no simultaneous readers and writers
    /\ Cardinality(writers) <= 1        \* at most one writer

\* ----------------------------------------------------------------------
\* Liveness property: every process eventually reads and eventually writes
\* (expressed as two separate weak fairness properties)
\* ----------------------------------------------------------------------
Liveness ==
    /\ \A p \in Actors : <> (p \in readers)
    /\ \A p \in Actors : <> (p \in writers)

====