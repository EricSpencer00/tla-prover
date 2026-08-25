---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* Set of processes (actors)
n == 1..NumActors
Proc == n

\* Request record type
Req == [type : {"Read","Write"}, proc : Proc]

VARIABLES Readers, Writers, Queue

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue = << >>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Readers \subseteq Proc
    /\ Writers \subseteq Proc
    /\ Cardinality(Writers) <= 1
    /\ Queue \in Seq(Req)

\* ----------------------------------------------------------------------
\* Safety invariant: no simultaneous readers and writers, at most one writer
\* ----------------------------------------------------------------------
Safety ==
    /\ Readers \cap Writers = {}
    /\ Cardinality(Writers) <= 1

\* ----------------------------------------------------------------------
\* Action: a process requests to read
\* ----------------------------------------------------------------------
RequestRead(p) ==
    /\ p \in Proc
    /\ ~(\E q \in Queue: q.proc = p)            \* not already waiting
    /\ Queue' = Queue \o <<[type |-> "Read", proc |-> p]>>
    /\ UNCHANGED <<Readers, Writers>>

RequestReadAction == \E p \in Proc: RequestRead(p)

\* ----------------------------------------------------------------------
\* Action: a process requests to write
\* ----------------------------------------------------------------------
RequestWrite(p) ==
    /\ p \in Proc
    /\ ~(\E q \in Queue: q.proc = p)            \* not already waiting
    /\ Queue' = Queue \o <<[type |-> "Write", proc |-> p]>>
    /\ UNCHANGED <<Readers, Writers>>

RequestWriteAction == \E p \in Proc: RequestWrite(p)

\* ----------------------------------------------------------------------
\* Action: process the queue (grant access)
\* ----------------------------------------------------------------------
ProcessQueue ==
    /\ Queue # << >>
    /\ Writers = {}
    /\ LET front == Head(Queue) IN
          ( /\ front.type = "Read"
            /\ Readers' = Readers \cup {front.proc}
            /\ Writers' = Writers
            /\ Queue'   = Tail(Queue) )
       \/ ( /\ front.type = "Write"
            /\ Readers = {}
            /\ Writers' = {front.proc}
            /\ Readers' = Readers
            /\ Queue'   = Tail(Queue) )

\* ----------------------------------------------------------------------
\* Action: a reader stops
\* ----------------------------------------------------------------------
StopRead(p) ==
    /\ p \in Readers
    /\ Readers' = Readers \ {p}
    /\ UNCHANGED <<Writers, Queue>>

StopReadAction == \E p \in Readers: StopRead(p)

\* ----------------------------------------------------------------------
\* Action: a writer stops
\* ----------------------------------------------------------------------
StopWrite(p) ==
    /\ p \in Writers
    /\ Writers' = {}
    /\ UNCHANGED <<Readers, Queue>>

StopWriteAction == \E p \in Writers: StopWrite(p)

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ RequestReadAction
    \/ RequestWriteAction
    \/ ProcessQueue
    \/ StopReadAction
    \/ StopWriteAction

\* ----------------------------------------------------------------------
\* Weak fairness for all actions
\* ----------------------------------------------------------------------
Fairness ==
    /\ WF_vars(RequestReadAction)
    /\ WF_vars(RequestWriteAction)
    /\ WF_vars(ProcessQueue)
    /\ WF_vars(StopReadAction)
    /\ WF_vars(StopWriteAction)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Readers, Writers, Queue>> /\ Fairness

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Liveness ==
    /\ \A p \in Proc :
          <> (p \in Readers) /\ <> (p \in Writers)
    /\ \A p \in Proc :
          []<>(p \in Readers => <> (p \notin Readers))
    /\ \A p \in Proc :
          []<>(p \in Writers => <> (p \notin Writers))

====