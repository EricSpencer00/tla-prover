---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* The finite set of actor identifiers
n == 1 .. NumActors

VARIABLES Readers, Writers, Queue

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Req == [type : {"read", "write"}, proc : n]

\* Helper to check whether a process already has a pending request
InQueue(p) == \E i \in 1 .. Len(Queue) : Queue[i].proc = p

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
    \E p \in n :
        /\ ~ (p \in Readers)
        /\ ~ (p \in Writers)
        /\ ~ InQueue(p)
        /\ Readers' = Readers
        /\ Writers' = Writers
        /\ Queue'   = Append(Queue, [type |-> "read", proc |-> p])

RequestWrite ==
    \E p \in n :
        /\ ~ (p \in Readers)
        /\ ~ (p \in Writers)
        /\ ~ InQueue(p)
        /\ Readers' = Readers
        /\ Writers' = Writers
        /\ Queue'   = Append(Queue, [type |-> "write", proc |-> p])

ProcessQueue ==
    LET front == Queue[1] IN
    /\ Queue # <<>>                 \* queue non‑empty
    /\ Writers = {}                 \* no writer currently active
    /\ ( front.type = "read"
        \/ (front.type = "write" /\ Readers = {} ) )
    /\ IF front.type = "read"
          THEN /\ Readers' = Readers \cup {front.proc}
               /\ Writers' = Writers
               /\ Queue'   = Tail(Queue)
          ELSE /\ Readers' = Readers
               /\ Writers' = {front.proc}
               /\ Queue'   = Tail(Queue)

StopActivity ==
    \E p \in n :
        /\ p \in Readers \/ p \in Writers
        /\ Queue' = Queue
        /\ IF p \in Readers
              THEN /\ Readers' = Readers \ {p}
                   /\ Writers' = Writers
              ELSE /\ Readers' = Readers
                   /\ Writers' = {}

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == RequestRead \/ RequestWrite \/ ProcessQueue \/ StopActivity

\* ----------------------------------------------------------------------
\* State variables tuple
\* ----------------------------------------------------------------------
vars == <<Readers, Writers, Queue>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars /\ 
    WF_vars(RequestRead) /\
    WF_vars(RequestWrite) /\
    WF_vars(ProcessQueue) /\
    WF_vars(StopActivity)

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Queue \in Seq(Req)
    /\ Cardinality(Writers) <= 1

\* ----------------------------------------------------------------------
\* Safety invariant
\* ----------------------------------------------------------------------
Safety ==
    /\ (Writers = {} \/ Readers = {})          \* no simultaneous readers & writers
    /\ Cardinality(Writers) <= 1               \* at most one writer

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Liveness ==
    \A p \in n : <> (p \in Readers) /\ <> (p \in Writers)

====