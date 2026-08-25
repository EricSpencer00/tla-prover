---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* Alias for the number of actors (the .cfg will substitute a concrete set for n)
n == NumActors

\* Set of process identifiers
Proc == 1..NumActors

\* Type of a request record
Req == [type : {"read","write"}, pid : Proc]

VARIABLES Readers, Writers, Queue

vars == << Readers, Writers, Queue >>

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = <<>>

\* ----------------------------------------------------------------------
\* Action: a process requests to read
\* ----------------------------------------------------------------------
RequestRead ==
    \E p \in Proc :
        /\ p \notin Readers
        /\ p \notin Writers
        /\ ~(\E q \in Queue : q.pid = p)           \* not already waiting
        /\ Readers' = Readers
        /\ Writers' = Writers
        /\ Queue'   = Append(Queue, [type |-> "read", pid |-> p])

\* ----------------------------------------------------------------------
\* Action: a process requests to write
\* ----------------------------------------------------------------------
RequestWrite ==
    \E p \in Proc :
        /\ p \notin Readers
        /\ p \notin Writers
        /\ ~(\E q \in Queue : q.pid = p)           \* not already waiting
        /\ Readers' = Readers
        /\ Writers' = Writers
        /\ Queue'   = Append(Queue, [type |-> "write", pid |-> p])

\* ----------------------------------------------------------------------
\* Action: serve the request at the head of the queue (read case)
\* ----------------------------------------------------------------------
ProcessRead ==
    /\ Queue # <<>>
    /\ Head(Queue).type = "read"
    /\ Writers = {}                                 \* no writer active
    /\ Readers' = Readers \cup {Head(Queue).pid}
    /\ Writers' = Writers
    /\ Queue'   = Tail(Queue)

\* ----------------------------------------------------------------------
\* Action: serve the request at the head of the queue (write case)
\* ----------------------------------------------------------------------
ProcessWrite ==
    /\ Queue # <<>>
    /\ Head(Queue).type = "write"
    /\ Writers = {}                                 \* no writer active
    /\ Readers = {}                                 \* no readers active
    /\ Writers' = {Head(Queue).pid}
    /\ Readers' = Readers
    /\ Queue'   = Tail(Queue)

ProcessQueue == ProcessRead \/ ProcessWrite

\* ----------------------------------------------------------------------
\* Action: a reader stops
\* ----------------------------------------------------------------------
StopRead ==
    \E p \in Readers :
        /\ Readers' = Readers \ {p}
        /\ Writers' = Writers
        /\ Queue'   = Queue

\* ----------------------------------------------------------------------
\* Action: a writer stops
\* ----------------------------------------------------------------------
StopWrite ==
    \E p \in Writers :
        /\ Writers' = {}
        /\ Readers' = Readers
        /\ Queue'   = Queue

Stop == StopRead \/ StopWrite

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == RequestRead \/ RequestWrite \/ ProcessQueue \/ Stop

\* ----------------------------------------------------------------------
\* Specification (with weak fairness on all actions)
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars
        /\ WF_vars(RequestRead)
        /\ WF_vars(RequestWrite)
        /\ WF_vars(ProcessQueue)
        /\ WF_vars(Stop)

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Readers \subseteq Proc
    /\ Writers \subseteq Proc
    /\ Cardinality(Writers) <= 1
    /\ Readers \cap Writers = {}
    /\ Queue \in Seq(Req)
    /\ \A i \in 1..Len(Queue) :
          LET rq == Queue[i] IN
              /\ rq.type \in {"read","write"}
              /\ rq.pid \in Proc

\* ----------------------------------------------------------------------
\* Safety invariant (no simultaneous readers & writers, at most one writer)
\* ----------------------------------------------------------------------
Safety ==
    /\ (Writers = {} \/ Readers = {})
    /\ Cardinality(Writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness property
\*   - every process eventually reads and eventually writes
\*   - every active reader eventually stops
\*   - every active writer eventually stops
\* ----------------------------------------------------------------------
Liveness ==
    \A p \in Proc :
        (<> (p \in Readers) /\ <> (p \in Writers) /\
         [] (p \in Readers => <> (p \notin Readers)) /\
         [] (p \in Writers => <> (p \notin Writers)))

\* ----------------------------------------------------------------------
\* The set of invariants and the property to be checked (as required by the .cfg)
\* ----------------------------------------------------------------------
INVARIANT TypeOK
INVARIANT Safety
PROPERTY Liveness

====