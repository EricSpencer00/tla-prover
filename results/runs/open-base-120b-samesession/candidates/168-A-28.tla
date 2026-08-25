---- MODULE ReadersWriters ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT NumActors

\* Set of actor identifiers (1..NumActors)
n == 1 .. NumActors

\* Types
Req == [type : {"read", "write"}, proc : n]

\* Variables
VARIABLES Readers, Writers, Queue

\* Helper definitions
QueueProcs == { r.proc : r \in SeqToSet(Queue) }

\* Initial state
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = <<>>

\* Action: a process requests a read
RequestRead(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ p \notin QueueProcs
    /\ Queue' = Append(Queue, [type |-> "read", proc |-> p])
    /\ Readers' = Readers
    /\ Writers' = Writers

\* Action: a process requests a write
RequestWrite(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ p \notin QueueProcs
    /\ Queue' = Append(Queue, [type |-> "write", proc |-> p])
    /\ Readers' = Readers
    /\ Writers' = Writers

\* Action: the first request in the queue is processed
ProcessQueue ==
    /\ Queue # <<>>
    /\ Writers = {}
    /\ LET front == Head(Queue) IN
       /\ ( front.type = "read"
            /\ Readers' = Readers \cup {front.proc}
            /\ Writers' = Writers
            /\ Queue'   = Tail(Queue) )
        \/ ( front.type = "write"
            /\ Readers = {}
            /\ Writers' = Writers \cup {front.proc}
            /\ Readers' = Readers
            /\ Queue'   = Tail(Queue) )

\* Action: a process stops its current activity
Stop(p) ==
    /\ p \in Readers \/ p \in Writers
    /\ IF p \in Readers THEN
          /\ Readers' = Readers \ {p}
          /\ Writers' = Writers
       ELSE
          /\ Readers' = Readers
          /\ Writers' = Writers \ {p}
    /\ Queue' = Queue

\* Next-state relation
Next ==
    \/ \E p \in n : RequestRead(p)
    \/ \E p \in n : RequestWrite(p)
    \/ ProcessQueue
    \/ \E p \in n : Stop(p)

\* Variables tuple for stuttering
vars == <<Readers, Writers, Queue>>

\* Weak fairness for all actions
Fairness ==
    /\ \A p \in n : WF_vars(RequestRead(p))
    /\ \A p \in n : WF_vars(RequestWrite(p))
    /\ WF_vars(ProcessQueue)
    /\ \A p \in n : WF_vars(Stop(p))

\* Specification
Spec ==
    Init /\ [][Next]_vars /\ Fairness

\* Type correctness invariant
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Queue   \in Seq(Req)
    /\ Readers \cap Writers = {}

\* Safety invariant
Safety ==
    /\ Readers \cap Writers = {}
    /\ Cardinality(Writers) <= 1

\* Liveness property
Liveness ==
    /\ \A p \in n : <> (p \in Readers)          \* every process eventually reads
    /\ \A p \in n : <> (p \in Writers)          \* every process eventually writes
    /\ \A p \in n : [] (p \in Readers => <> (p \notin Readers))  \* readers eventually stop
    /\ \A p \in n : [] (p \in Writers => <> (p \notin Writers))  \* writers eventually stop

====