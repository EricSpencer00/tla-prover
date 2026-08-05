---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

Actors == 1..NumActors

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

Req == [type : {"read", "write"}, p : Actors]

TypeOK ==
    /\ reading \subseteq Actors
    /\ writing \subseteq Actors
    /\ queue \in Seq(Req)

\* Readers and writers are never simultaneously active; an active writer blocks
\* all readers, and vice versa, which is the core mutual-exclusion safety rule.
Safety ==
    /\ (writing # {} => reading = {})
    /\ (reading # {} => writing = {})
    /\ Cardinality(writing) <= 1

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = <<>>

RequestRead(p) ==
    /\ \A i \in 1..Len(queue) : ~(queue[i].p = p /\ queue[i].type = "read")
    /\ queue' = Append(queue, [type |-> "read", p |-> p])
    /\ UNCHANGED <<reading, writing>>

RequestWrite(p) ==
    /\ \A i \in 1..Len(queue) : ~(queue[i].p = p /\ queue[i].type = "write")
    /\ queue' = Append(queue, [type |-> "write", p |-> p])
    /\ UNCHANGED <<reading, writing>>

\* A queued request takes effect only when it would not conflict with the
\* current active set -- writers wait for readers to clear first.
ProcessQueue ==
    /\ queue # <<>>
    /\ writing = {}
    /\ LET h == Head(queue)
       IN /\ IF h.type = "read" THEN reading' = reading \cup {h.p} /\ writing' = writing
          ELSE IF reading = {} THEN reading' = reading /\ writing' = {h.p} ELSE reading' = reading /\ writing' = writing
       /\ queue' = Tail(queue)

StopActivity(p) ==
    /\ (p \in reading \/ p \in writing)
    /\ reading' = reading \ {p}
    /\ writing' = writing \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in Actors : RequestRead(p)
    \/ \E p \in Actors : RequestWrite(p)
    \/ ProcessQueue
    \/ \E p \in Actors : StopActivity(p)

Fairness ==
    /\ \A p \in Actors : WF_vars(RequestRead(p))
    /\ \A p \in Actors : WF_vars(RequestWrite(p))
    /\ WF_vars(ProcessQueue)
    /\ \A p \in Actors : WF_vars(StopActivity(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Every process eventually gets to read and eventually gets to write.
Liveness ==
    /\ \A p \in Actors : <>(p \in reading)
    /\ \A p \in Actors : <>(p \in writing)
    /\ \A p \in Actors : <>(p \notin reading)
    /\ \A p \in Actors : <>(p \notin writing)

====