---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES activeReaders, activeWriters, queue

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Processes == 1 .. NumActors
ReadReq   == "R"
WriteReq  == "W"
ReqTypes  == {ReadReq, WriteReq}
Request   == [type : ReqTypes, proc : Processes]

\* ----------------------------------------------------------------------
\* Types for readability
\* ----------------------------------------------------------------------
ActiveReadersSet == SUBSET Processes
ActiveWritersSet == SUBSET Processes
QueueSet         == Seq(Request)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ activeReaders = {}
    /\ activeWriters = {}
    /\ queue = <<>>

\* ----------------------------------------------------------------------
\* Helper: is the request at the head of the queue?
\* ----------------------------------------------------------------------
HeadReq == IF Len(queue) = 0 THEN [type |-> "", proc |-> 0] ELSE Head(queue)

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
RequestRead(proc) ==
    /\ proc \in Processes
    /\ proc \notin { r.proc : r \in queue : r.type = ReadReq }
    /\ proc \notin activeReaders
    /\ proc \notin activeWriters
    /\ queue' = Append(queue, [type |-> ReadReq, proc |-> proc])
    /\ UNCHANGED <<activeReaders, activeWriters>>

RequestWrite(proc) ==
    /\ proc \in Processes
    /\ proc \notin { r.proc : r \in queue : r.type = WriteReq }
    /\ proc \notin activeReaders
    /\ proc \notin activeWriters
    /\ queue' = Append(queue, [type |-> WriteReq, proc |-> proc])
    /\ UNCHANGED <<activeReaders, activeWriters>>

BeginOperation ==
    /\ Len(queue) > 0
    /\ activeWriters = {}        \* no writer active
    /\ LET r == Head(queue) IN
       IF r.type = ReadReq THEN
          /\ activeReaders' = activeReaders \cup {r.proc}
          /\ activeWriters' = {}
          /\ queue' = Tail(queue)
       ELSE \* WriteReq
          /\ activeReaders = {}
          /\ activeWriters' = {r.proc}
          /\ queue' = Tail(queue)
    /\ UNCHANGED activeReaders, activeWriters, queue

StopActivity(proc) ==
    /\ proc \in Processes
    /\ \/ proc \in activeReaders
       \/ proc \in activeWriters
    /\ IF proc \in activeReaders
          THEN activeReaders' = activeReaders \ {proc}
                /\ activeWriters' = activeWriters
          ELSE activeWriters' = {}            \* at most one writer
                /\ activeReaders' = activeReaders
    /\ UNCHANGED queue

Next ==
    \/ \E p \in Processes: RequestRead(p)
    \/ \E p \in Processes: RequestWrite(p)
    \/ BeginOperation
    \/ \E p \in Processes: StopActivity(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<activeReaders, activeWriters, queue>>

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
TypeOK ==
    /\ activeReaders \in ActiveReadersSet
    /\ activeWriters \in ActiveWritersSet
    /\ activeWriters \subseteq Processes
    /\ activeWriters \subseteq { r.proc : r \in queue : r.type = WriteReq } = FALSE
    /\ queue \in QueueSet

\* ----------------------------------------------------------------------
\* Safety invariant
\* ----------------------------------------------------------------------
Safety ==
    /\ ~(activeWriters # {} /\ activeReaders # {})
    /\ Cardinality(activeWriters) <= 1

\* ----------------------------------------------------------------------
\* Liveness property (weak fairness of all actions)
\* ----------------------------------------------------------------------
Liveness ==
    WF_vars(Next)

\* ----------------------------------------------------------------------
\* Theorems (optional, but help TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Safety

====