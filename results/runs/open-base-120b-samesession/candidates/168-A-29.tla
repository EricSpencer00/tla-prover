---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\* Set of actor identifiers (the .cfg file will substitute a concrete set for n)
\* ----------------------------------------------------------------------
n == 1..NumActors

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
ReqRec == [proc : n, type : {"read", "write"}]

VARIABLES Readers, Writers, Queue

\* ----------------------------------------------------------------------
\* Helper predicates
\* ----------------------------------------------------------------------
InQueue(p) == 
  \E i \in 1..Len(Queue) : Queue[i].proc = p

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
  /\ ~InQueue(p)
  /\ p \notin Readers
  /\ p \notin Writers
  /\ Queue' = Append(Queue, [proc |-> p, type |-> "read"])
  /\ UNCHANGED <<Readers, Writers>>

RequestWrite(p) ==
  /\ p \in n
  /\ ~InQueue(p)
  /\ p \notin Readers
  /\ p \notin Writers
  /\ Queue' = Append(Queue, [proc |-> p, type |-> "write"])
  /\ UNCHANGED <<Readers, Writers>>

Begin ==
  /\ Queue # <<>>
  /\ Writers = {}                                    \* no writer currently active
  /\ LET front == Head(Queue) IN
       /\ (front.type = "read" => 
             /\ Readers' = Readers \cup {front.proc}
             /\ Writers' = Writers
          )
       /\ (front.type = "write" => 
             /\ Readers = {}                      \* no readers active for a write
             /\ Writers' = {front.proc}
          )
  /\ Queue' = Tail(Queue)
  /\ UNCHANGED <<>>

Stop(p) ==
  /\ p \in n
  /\ (p \in Readers \/ p \in Writers)
  /\ IF p \in Readers THEN
        /\ Readers' = Readers \ {p}
        /\ Writers' = Writers
     ELSE
        /\ Readers' = Readers
        /\ Writers' = {}
  /\ UNCHANGED <<Queue>>

\* ----------------------------------------------------------------------
\* Action aggregations for fairness
\* ----------------------------------------------------------------------
RequestReadAction == \E p \in n : RequestRead(p)
RequestWriteAction == \E p \in n : RequestWrite(p)
StopAction == \E p \in n : Stop(p)
BeginAction == Begin

Next ==
  \/ RequestReadAction
  \/ RequestWriteAction
  \/ BeginAction
  \/ StopAction

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
  Init
  /\ [][Next]_<<Readers, Writers, Queue>>
  /\ WF_vars(RequestReadAction)
  /\ WF_vars(RequestWriteAction)
  /\ WF_vars(BeginAction)
  /\ WF_vars(StopAction)

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Readers \subseteq n
  /\ Writers \subseteq n
  /\ Cardinality(Writers) <= 1
  /\ Queue \in Seq(ReqRec)

\* ----------------------------------------------------------------------
\* Safety invariant (readers and writers never active together, at most one writer)
\* ----------------------------------------------------------------------
Safety ==
  /\ Writers \cap Readers = {}
  /\ Cardinality(Writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness properties
\*   - every process eventually reads and eventually writes
\*   - every active reader eventually stops
\*   - every active writer eventually stops
\* ----------------------------------------------------------------------
Liveness ==
  \A p \in n :
    (<> (p \in Readers)               \* eventually reads
     /\ <> (p \in Writers)            \* eventually writes
     /\ [] (p \in Readers => <> (p \notin Readers))
     /\ [] (p \in Writers => <> (p \notin Writers)))

====