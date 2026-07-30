---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

NoOne == 0 - 1

Processes == 1..NumActors
Acts == {"read", "write"}
Reqs == [act : Acts, p : Processes]

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

TypeOK ==
    /\ reading \subseteq Processes
    /\ writing \subseteq Processes
    /\ queue \in Seq(Reqs)

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = <<>>

EnqueueRead(p) ==
    /\ \A i \in 1..Len(queue) : queue[i].p # p
    /\ queue' = Append(queue, [act |-> "read", p |-> p])
    /\ UNCHANGED <<reading, writing>>

EnqueueWrite(p) ==
    /\ \A i \in 1..Len(queue) : queue[i].p # p
    /\ queue' = Append(queue, [act |-> "write", p |-> p])
    /\ UNCHANGED <<reading, writing>>

ProcessQueue ==
    /\ Len(queue) > 0
    /\ writing = {}
    /\ LET req == Head(queue)
           rest == Tail(queue)
       IN
          /\ IF req.act = "read"
             THEN reading' = reading \cup {req.p}
             ELSE /\ req.act = "write"
                  /\ reading = {}
                  /\ writing' = writing \cup {req.p}
          /\ queue' = rest
    /\ UNCHANGED <<reading, writing>>

StopActivity(p) ==
    \/ /\ p \in reading
       /\ reading' = reading \ {p}
       /\ UNCHANGED <<writing, queue>>
    \/ /\ p \in writing
       /\ writing' = writing \ {p}
       /\ UNCHANGED <<reading, queue>>

Next ==
    \/ \E p \in Processes : EnqueueRead(p)
    \/ \E p \in Processes : EnqueueWrite(p)
    \/ ProcessQueue
    \/ \E p \in Processes : StopActivity(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in Processes : EnqueueRead(p))
    /\ WF_vars(\E p \in Processes : EnqueueWrite(p))
    /\ WF_vars(ProcessQueue)
    /\ WF_vars(\E p \in Processes : StopActivity(p))

Safety ==
    /\ (writing # {}) => (reading = {})
    /\ (reading # {}) => (writing = {})
    /\ Cardinality(writing) <= 1

Liveness ==
    /\ \A p \in Processes : (p \in reading) ~> (p \notin reading)
    /\ \A p \in Processes : (p \in writing) ~> (p \notin writing)

====