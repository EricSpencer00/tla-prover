---- MODULE ReadersWriters ----
EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\* Operator used by the .cfg file to instantiate the constant NumActors
\* (the cfg will replace NumActors with the value of n)
\* ----------------------------------------------------------------------
n == 1..5

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES Readers, Writers, Queue

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ReaderType == "read"
WriterType == "write"

Request == [proc : NumActors, type : {"read","write"}]

\* A process is idle when it is not reading, not writing, and not waiting
Idle(p) == 
    /\ p \notin Readers
    /\ p \notin Writers
    /\ \A r \in Queue : r.proc # p

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Readers \subseteq NumActors
    /\ Writers \subseteq NumActors
    /\ \A w \in Writers : Cardinality(Writers) = 1
    /\ Queue \in Seq(Request)

\* ----------------------------------------------------------------------
\* Safety invariant (readers and writers are never simultaneously active,
\* and at most one writer)
\* ----------------------------------------------------------------------
Safety ==
    /\ (Writers = {} \/ Readers = {})
    /\ Cardinality(Writers) <= 1

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = <<>>

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
RequestRead ==
    \E p \in Idle(NumActors) :
        /\ Queue' = Append(Queue, [proc |-> p, type |-> ReaderType])
        /\ UNCHANGED <<Readers, Writers>>

RequestWrite ==
    \E p \in Idle(NumActors) :
        /\ Queue' = Append(Queue, [proc |-> p, type |-> WriterType])
        /\ UNCHANGED <<Readers, Writers>>

ProcessQueue ==
    /\ Queue # <<>>
    /\ LET front == Head(Queue) IN
       IF front.type = ReaderType THEN
          /\ Writers = {}
          /\ Readers' = Readers \cup {front.proc}
          /\ Writers' = Writers
          /\ Queue'   = Tail(Queue)
       ELSE
          /\ Readers = {}
          /\ Writers' = Writers \cup {front.proc}
          /\ Readers' = Readers
          /\ Queue'   = Tail(Queue)

Stop ==
    \E p \in (Readers \cup Writers) :
        /\ IF p \in Readers THEN
              /\ Readers' = Readers \ {p}
              /\ Writers' = Writers
           ELSE
              /\ Writers' = Writers \ {p}
              /\ Readers' = Readers
        /\ UNCHANGED Queue

Next ==
    \/ RequestRead
    \/ RequestWrite
    \/ ProcessQueue
    \/ Stop

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<Readers, Writers, Queue>>

Spec ==
    Init /\ [][Next]_vars
          /\ WF_vars(RequestRead)
          /\ WF_vars(RequestWrite)
          /\ WF_vars(ProcessQueue)
          /\ WF_vars(Stop)

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Liveness ==
    /\ \A p \in NumActors : <> (p \in Readers) /\ <> (p \in Writers)
    /\ \A p \in NumActors : (p \in Readers) => <> (p \notin Readers)
    /\ \A p \in NumActors : (p \in Writers) => <> (p \notin Writers)

====