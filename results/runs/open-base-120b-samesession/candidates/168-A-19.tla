---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, TLC

CONSTANT NumActors

\* Number of actors, to be instantiated in the .cfg file
n == 1 .. NumActors

VARIABLES Readers, Writers, Queue

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
vars == << Readers, Writers, Queue >>

\* The front element of the queue (defined only when Len(Queue) > 0)
Front(q) == q[1]

\* ----------------------------------------------------------------------
\* State predicates
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Readers \cap Writers = {}
    /\ \A i \in DOMAIN Queue :
          /\ Queue[i].proc \in n
          /\ Queue[i].type \in {"read", "write"}

Safety ==
    /\ Readers \cap Writers = {}
    /\ Cardinality(Writers) <= 1

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue = << >>

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* A process may request a read
RequestRead(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ \A i \in DOMAIN Queue : Queue[i].proc # p
    /\ Queue' = Append(Queue, [proc |-> p, type |-> "read"])
    /\ UNCHANGED << Readers, Writers >>

\* A process may request a write
RequestWrite(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ \A i \in DOMAIN Queue : Queue[i].proc # p
    /\ Queue' = Append(Queue, [proc |-> p, type |-> "write"])
    /\ UNCHANGED << Readers, Writers >>

\* Process the request at the head of the queue
ProcessQueue ==
    /\ Len(Queue) > 0
    /\ Writers = {}
    /\ LET fr == Front(Queue) IN
       IF fr.type = "read" THEN
          /\ fr.proc \notin Readers \cup Writers
          /\ Readers' = Readers \cup {fr.proc}
          /\ Writers' = Writers
          /\ Queue'   = Tail(Queue)
       ELSE
          /\ fr.type = "write"
          /\ Readers = {}
          /\ fr.proc \notin Readers \cup Writers
          /\ Writers' = Writers \cup {fr.proc}
          /\ Readers' = Readers
          /\ Queue'   = Tail(Queue)
    /\ UNCHANGED << >>

\* A process may stop its current activity
Stop(p) ==
    \/ /\ p \in Readers
       /\ Readers' = Readers \ {p}
       /\ Writers' = Writers
       /\ UNCHANGED Queue
    \/ /\ p \in Writers
       /\ Writers' = Writers \ {p}
       /\ Readers' = Readers
       /\ UNCHANGED Queue

\* ----------------------------------------------------------------------
\* Action aggregations for fairness
\* ----------------------------------------------------------------------
ReadReq == \E p \in n : RequestRead(p)
WriteReq == \E p \in n : RequestWrite(p)
StopAct == \E p \in n : Stop(p)

Next == ReadReq \/ WriteReq \/ ProcessQueue \/ StopAct

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(ReadReq) /\ WF_vars(WriteReq) /\ WF_vars(ProcessQueue) /\ WF_vars(StopAct)

\* ----------------------------------------------------------------------
\* Invariants and properties
\* ----------------------------------------------------------------------
INVARIANT TypeOK
INVARIANT Safety

Liveness == \A p \in n : (<> (p \in Readers) /\ <> (p \in Writers))

====