---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\* Derived constant used by the .cfg file (substituted for NumActors)
n == 1 .. NumActors

\* ----------------------------------------------------------------------
\* Types
Req == [type : {"read", "write"}, proc : n]

\* ----------------------------------------------------------------------
\* Variables
VARIABLES Readers, Writers, Queue

vars == << Readers, Writers, Queue >>

\* ----------------------------------------------------------------------
\* Helper definitions
QueueProcs == { q.proc : q \in Queue }

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = << >>

\* ----------------------------------------------------------------------
\* Parameterised actions
ReqRead(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ p \notin QueueProcs
    /\ Queue' = Append(Queue, [type |-> "read", proc |-> p])
    /\ Readers' = Readers
    /\ Writers' = Writers

ReqWrite(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ p \notin QueueProcs
    /\ Queue' = Append(Queue, [type |-> "write", proc |-> p])
    /\ Readers' = Readers
    /\ Writers' = Writers

ProcQueue ==
    /\ Queue # <<>>
    /\ Writers = {}
    /\ LET front == Head(Queue) IN
       IF front.type = "read" THEN
          /\ Readers' = Readers \cup {front.proc}
          /\ Writers' = Writers
          /\ Queue'   = Tail(Queue)
       ELSE
          /\ front.type = "write"
          /\ Readers = {}
          /\ Writers' = Writers \cup {front.proc}
          /\ Readers' = Readers
          /\ Queue'   = Tail(Queue)

StopAct(p) ==
    /\ p \in Readers \/ p \in Writers
    /\ Readers' = IF p \in Readers THEN Readers \ {p} ELSE Readers
    /\ Writers' = IF p \in Writers THEN Writers \ {p} ELSE Writers
    /\ Queue'   = Queue

\* ----------------------------------------------------------------------
\* Unguarded (existential) actions used in Next and fairness
RequestRead == \E p \in n: ReqRead(p)
RequestWrite == \E p \in n: ReqWrite(p)
Stop == \E p \in n: StopAct(p)

\* ----------------------------------------------------------------------
\* Next-state relation
Next ==
    \/ RequestRead
    \/ RequestWrite
    \/ ProcQueue
    \/ Stop

\* ----------------------------------------------------------------------
\* Specification
Spec ==
    Init /\ [][Next]_vars
    /\ WF_vars(RequestRead)
    /\ WF_vars(RequestWrite)
    /\ WF_vars(ProcQueue)
    /\ WF_vars(Stop)

\* ----------------------------------------------------------------------
\* Type correctness invariant
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Readers \cap Writers = {}
    /\ Queue \in Seq(Req)
    /\ \A i, j \in DOMAIN Queue :
          i # j => Queue[i].proc # Queue[j].proc

\* ----------------------------------------------------------------------
\* Safety invariant
Safety ==
    /\ (Writers = {} \/ Readers = {})
    /\ Cardinality(Writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness property
Liveness ==
    \A p \in n :
        /\ <> (p \in Readers)               \* every process eventually reads
        /\ <> (p \in Writers)               \* every process eventually writes
        /\ [] (p \in Readers => <> (p \notin Readers))   \* readers eventually stop
        /\ [] (p \in Writers => <> (p \notin Writers))   \* writers eventually stop

=============================================================================