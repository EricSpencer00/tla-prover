---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, TLC

CONSTANT NumActors

\* ----------------------------------------------------------------------
\* Types and constants
\* ----------------------------------------------------------------------
Actors == 1..NumActors

Request == [type : {"read","write"}, proc : Actors]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES readers, writers, queue

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
IsRead(req) == req.type = "read"
IsWrite(req) == req.type = "write"

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = << >>

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* A process that is not already waiting (i.e., has no pending request) may
\* request read access.
RequestRead(p) ==
    /\ p \in Actors
    /\ ~(\E i \in 1..Len(queue): queue[i].proc = p)
    /\ queue' = Append(queue, [type |-> "read", proc |-> p])
    /\ UNCHANGED << readers, writers >>

\* A process that is not already waiting may request write access.
RequestWrite(p) ==
    /\ p \in Actors
    /\ ~(\E i \in 1..Len(queue): queue[i].proc = p)
    /\ queue' = Append(queue, [type |-> "write", proc |-> p])
    /\ UNCHANGED << readers, writers >>

\* The process at the front of the queue may begin its requested activity.
\* No writer may be active for any request to start.
Begin ==
    /\ Len(queue) > 0
    /\ writers = {}               \* no writer currently active
    /\ LET front == queue[1] IN
       IF front.type = "read" THEN
          /\ readers' = readers \cup {front.proc}
          /\ writers' = writers
          /\ queue'   = Tail(queue)
       ELSE \* front.type = "write"
          /\ readers = {}          \* no readers must be active
          /\ writers' = writers \cup {front.proc}
          /\ queue'   = Tail(queue)
    /\ UNCHANGED << >>

\* Any active reader may stop.
StopRead(p) ==
    /\ p \in readers
    /\ readers' = readers \ {p}
    /\ UNCHANGED << writers, queue >>

\* Any active writer may stop.
StopWrite(p) ==
    /\ p \in writers
    /\ writers' = writers \ {p}
    /\ UNCHANGED << readers, queue >>

Next ==
    \/ \E p \in Actors: RequestRead(p)
    \/ \E p \in Actors: RequestWrite(p)
    \/ Begin
    \/ \E p \in Actors: StopRead(p)
    \/ \E p \in Actors: StopWrite(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<readers, writers, queue>>

\* ----------------------------------------------------------------------
\* Type invariant (helps TLC)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ writers \subseteq { w \in Actors : w \in writers } \cap { w \in Actors : w \in writers } \* trivial, just to keep the shape
    /\ queue \in Seq(Request)

\* ----------------------------------------------------------------------
\* Safety invariant (the required safety property)
\* ----------------------------------------------------------------------
Safety ==
    /\ \A p \in writers: p \notin readers
    /\ Cardinality(writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness property (required but not used as an invariant)
\* ----------------------------------------------------------------------
Liveness == 
    /\ WF_vars(RequestRead)
    /\ WF_vars(RequestWrite)
    /\ WF_vars(Begin)
    /\ WF_vars(StopRead)
    /\ WF_vars(StopWrite)

\* ----------------------------------------------------------------------
\* Theorem (optional, but ensures Spec implies Safety)
\* ----------------------------------------------------------------------
THEOREM Spec => []Safety

====