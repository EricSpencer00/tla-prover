---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\* Derived constant used by the .cfg file (substituted for NumActors)
\* ----------------------------------------------------------------------
n == 1..NumActors

VARIABLES Readers, Writers, Queue

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
Req == [proc : n, type : {"read", "write"}]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Pending(p) == \E i \in 1..Len(Queue) : Queue[i].proc = p

Front == Queue[1]

Tail(q) == 
  IF Len(q) = 0 THEN <<>>
  ELSE SubSeq(q, 2, Len(q))

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
  /\ ~Pending(p)
  /\ Queue' = Queue \o <<[proc |-> p, type |-> "read"]>>
  /\ UNCHANGED <<Readers, Writers>>

RequestWrite(p) ==
  /\ p \in n
  /\ p \notin Readers
  /\ p \notin Writers
  /\ ~Pending(p)
  /\ Queue' = Queue \o <<[proc |-> p, type |-> "write"]>>
  /\ UNCHANGED <<Readers, Writers>>

ProcessQueue ==
  /\ Len(Queue) > 0
  /\ Writers = {}
  /\ LET f == Front IN
       IF f.type = "read" THEN
         /\ Readers' = Readers \cup {f.proc}
         /\ Writers' = Writers
         /\ Queue'   = Tail(Queue)
       ELSE
         /\ f.type = "write"
         /\ Readers = {}
         /\ Writers' = Writers \cup {f.proc}
         /\ Readers' = Readers
         /\ Queue'   = Tail(Queue)
       END

Stop(p) ==
  /\ p \in Readers \/ p \in Writers
  /\ IF p \in Readers THEN
        /\ Readers' = Readers \ {p}
        /\ Writers' = Writers
     ELSE
        /\ Readers' = Readers
        /\ Writers' = Writers \ {p}
     END
  /\ UNCHANGED Queue

Next ==
  \/ \E p \in n : RequestRead(p)
  \/ \E p \in n : RequestWrite(p)
  \/ ProcessQueue
  \/ \E p \in n : Stop(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_<<Readers, Writers, Queue>>
  /\ \A p \in n : WF_<<Readers, Writers, Queue>>(RequestRead(p))
  /\ \A p \in n : WF_<<Readers, Writers, Queue>>(RequestWrite(p))
  /\ WF_<<Readers, Writers, Queue>>(ProcessQueue)
  /\ \A p \in n : WF_<<Readers, Writers, Queue>>(Stop(p))

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Readers \subseteq n
  /\ Writers \subseteq n
  /\ Readers \cap Writers = {}
  /\ Queue \in Seq(Req)

Safety ==
  /\ (Writers = {} \/ Readers = {})
  /\ Cardinality(Writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Liveness ==
  \A p \in n :
    /\ <> (p \in Readers)          \* p eventually reads
    /\ <> (p \in Writers)          \* p eventually writes
    /\ [] (p \in Readers => <> (p \notin Readers)) \* readers eventually stop
    /\ [] (p \in Writers => <> (p \notin Writers)) \* writers eventually stop

====