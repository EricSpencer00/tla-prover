---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

\* The finite set of actor identifiers
n == 1 .. NumActors

\* Types
Proc == n
Request == [type : {"read", "write"}, proc : Proc]

VARIABLES readers, writers, queue

\*=================================================================
\* Initial state
\*=================================================================
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = << >>

\*=================================================================
\* Type correctness
\*=================================================================
TypeOK ==
    /\ readers \subseteq Proc
    /\ writers \subseteq Proc
    /\ Disjoint(readers, writers)
    /\ queue \in Seq(Request)
    /\ \A r \in queue : /\ r.proc \in Proc
                         /\ r.type \in {"read", "write"}

\*=================================================================
\* Actions
\*=================================================================

\* A process requests read access
ReadReq(p) ==
    /\ p \in Proc
    /\ p \notin readers
    /\ p \notin writers
    /\ \A r \in queue : r.proc # p
    /\ queue' = Append(queue, [type |-> "read", proc |-> p])
    /\ UNCHANGED <<readers, writers>>

\* A process requests write access
WriteReq(p) ==
    /\ p \in Proc
    /\ p \notin readers
    /\ p \notin writers
    /\ \A r \in queue : r.proc # p
    /\ queue' = Append(queue, [type |-> "write", proc |-> p])
    /\ UNCHANGED <<readers, writers>>

\* The first request in the queue is processed
ProcessQueue ==
    /\ queue # <<>>
    /\ writers = {}        \* no writer currently active
    LET head == Head(queue) IN
        /\ IF head.type = "read"
           THEN /\ readers' = readers \cup {head.proc}
                /\ writers' = writers
           ELSE /\ readers = {}               \* no readers for a writer to start
                /\ writers' = writers \cup {head.proc}
                /\ readers' = readers
        /\ queue' = Tail(queue)
    /\ UNCHANGED <<>>

\* An active reader or writer stops its activity
Stop(p) ==
    /\ p \in readers \/ p \in writers
    /\ IF p \in readers
          THEN /\ readers' = readers \ {p}
               /\ writers' = writers
          ELSE /\ readers' = readers
               /\ writers' = writers \ {p}
    /\ UNCHANGED queue

\*=================================================================
\* Next-state relation
\*=================================================================
ReadReqAction == \E p \in Proc : ReadReq(p)
WriteReqAction == \E p \in Proc : WriteReq(p)
StopAction == \E p \in Proc : Stop(p)

Next ==
    \/ ReadReqAction
    \/ WriteReqAction
    \/ ProcessQueue
    \/ StopAction

\*=================================================================
\* Specification
\*=================================================================
vars == <<readers, writers, queue>>

Spec ==
    Init /\
    [][Next]_vars /\
    WF_vars(ReadReqAction) /\
    WF_vars(WriteReqAction) /\
    WF_vars(ProcessQueue)   /\
    WF_vars(StopAction)

\*=================================================================
\* Safety invariant
\*=================================================================
Safety ==
    /\ (writers = {} \/ readers = {})      \* no simultaneous readers & writers
    /\ Cardinality(writers) <= 1           \* at most one writer

\*=================================================================
\* Liveness property
\*=================================================================
Liveness ==
    \A p \in Proc :
        <> (p \in readers) /\ <> (p \in writers)

\*=================================================================
\* The identifiers required by the .cfg file
\*=================================================================
INVARIANTS == TypeOK, Safety
PROPERTIES == Liveness

====