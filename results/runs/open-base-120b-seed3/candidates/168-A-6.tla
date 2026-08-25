---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT NumActors

\* Set of actor identifiers
n == 1 .. NumActors

\* Definition of a request record
Req == [type : {"read", "write"}, proc : n]

VARIABLES Readers, Writers, Queue

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Queue \in Seq(Req)

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
RequestRead(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ ~(\E i \in 1..Len(Queue):
            /\ Queue[i].proc = p
            /\ Queue[i].type = "read")
    /\ Queue' = Append(Queue, [type |-> "read", proc |-> p])
    /\ UNCHANGED <<Readers, Writers>>

RequestWrite(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ ~(\E i \in 1..Len(Queue):
            /\ Queue[i].proc = p
            /\ Queue[i].type = "write")
    /\ Queue' = Append(Queue, [type |-> "write", proc |-> p])
    /\ UNCHANGED <<Readers, Writers>>

ProcessQueue ==
    /\ Len(Queue) > 0
    /\ LET req == Queue[1] IN
       /\ IF req.type = "read" THEN
            /\ Writers = {}
            /\ Readers' = Readers \cup {req.proc}
            /\ Writers' = Writers
            /\ Queue'   = Tail(Queue)
          ELSE
            /\ req.type = "write"
            /\ Writers = {}
            /\ Readers = {}
            /\ Writers' = Writers \cup {req.proc}
            /\ Readers' = Readers
            /\ Queue'   = Tail(Queue)
    /\ UNCHANGED <<>>

Stop(p) ==
    /\ p \in n
    /\ (p \in Readers) \/ (p \in Writers)
    /\ IF p \in Readers THEN
          /\ Readers' = Readers \ {p}
          /\ Writers' = Writers
       ELSE
          /\ Readers' = Readers
          /\ Writers' = Writers \ {p}
    /\ UNCHANGED Queue

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in n: RequestRead(p)
    \/ \E p \in n: RequestWrite(p)
    \/ ProcessQueue
    \/ \E p \in n: Stop(p)

\* ----------------------------------------------------------------------
\* Fairness
\* ----------------------------------------------------------------------
RequestReadFair == \E p \in n: RequestRead(p)
RequestWriteFair == \E p \in n: RequestWrite(p)
StopFair == \E p \in n: Stop(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<Readers, Writers, Queue>>

Spec ==
    Init /\
    [][Next]_vars /\
    WF_vars(RequestReadFair) /\
    WF_vars(RequestWriteFair) /\
    WF_vars(ProcessQueue) /\
    WF_vars(StopFair)

\* ----------------------------------------------------------------------
\* Safety invariant
\* ----------------------------------------------------------------------
Safety ==
    /\ Readers \cap Writers = {}
    /\ Cardinality(Writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Liveness ==
    \A p \in n : (<> (p \in Readers) /\ <> (p \in Writers))

\* ----------------------------------------------------------------------
\* THEOREMS (required by the .cfg file)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Safety
THEOREM Spec => Liveness

=============================================================================