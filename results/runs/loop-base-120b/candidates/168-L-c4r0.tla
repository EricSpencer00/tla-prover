---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

\* ----------------------------------------------------------------------
\* Derived constant for the set of actor identifiers
\* ----------------------------------------------------------------------
n == 1..NumActors

VARIABLES Readers, Writers, Queue

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of processes that currently have a pending request in the queue
QueueProcs == { req.proc : req \in SeqToSet(Queue) }

\* Record constructors for requests
ReadReq(p)  == [type |-> "read",  proc |-> p]
WriteReq(p) == [type |-> "write", proc |-> p]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = << >>

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
RequestRead(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ p \notin QueueProcs
    /\ Queue' = Append(Queue, ReadReq(p))
    /\ UNCHANGED << Readers, Writers >>

RequestWrite(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ p \notin QueueProcs
    /\ Queue' = Append(Queue, WriteReq(p))
    /\ UNCHANGED << Readers, Writers >>

Begin ==
    /\ Queue # << >>                         \* queue not empty
    /\ LET front == Queue[1] IN
       IF front.type = "read" THEN
          /\ Writers = {}
          /\ Readers' = Readers \cup {front.proc}
          /\ Writers' = Writers
          /\ Queue'   = Tail(Queue)
       ELSE
          /\ front.type = "write"
          /\ Readers = {}
          /\ Writers' = Writers \cup {front.proc}
          /\ Readers' = Readers
          /\ Queue'   = Tail(Queue)
    /\ UNCHANGED << >>

Stop(p) ==
    /\ p \in Readers \/ p \in Writers
    /\ IF p \in Readers THEN
          /\ Readers' = Readers \ {p}
          /\ Writers' = Writers
       ELSE
          /\ Readers' = Readers
          /\ Writers' = Writers \ {p}
    /\ UNCHANGED Queue

Next ==
    \/ \E p \in n : RequestRead(p)
    \/ \E p \in n : RequestWrite(p)
    \/ Begin
    \/ \E p \in n : Stop(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == << Readers, Writers, Queue >>

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ \A req \in SeqToSet(Queue) :
          req.proc \in n /\ (req.type = "read" \/ req.type = "write")

Safety ==
    /\ (Writers = {} \/ Readers = {})
    /\ Cardinality(Writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Liveness ==
    \A p \in n :
        ( <> (p \in Readers)                \* eventually reads
        /\ <> (p \in Writers)                \* eventually writes
        /\ [] (p \in Readers => <> (p \notin Readers))   \* readers eventually stop
        /\ [] (p \in Writers => <> (p \notin Writers)) ) \* writers eventually stop

=============================================================================