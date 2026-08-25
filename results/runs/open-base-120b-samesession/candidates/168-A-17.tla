---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

\* Number of actors as a finite set 1..NumActors
n == 1..NumActors

\* Request record
Req == [type : {"R","W"}, proc : n]

VARIABLES Readers, Writers, Queue

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
vars == << Readers, Writers, Queue >>

QueueProcs == { q.proc : q \in SeqToSet(Queue) }

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
    /\ Readers' = Readers
    /\ Writers' = Writers
    /\ Queue'   = Append(Queue, [type |-> "R", proc |-> p])

RequestWrite(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ p \notin QueueProcs
    /\ Readers' = Readers
    /\ Writers' = Writers
    /\ Queue'   = Append(Queue, [type |-> "W", proc |-> p])

Begin ==
    /\ Queue # <<>>
    /\ Writers = {}
    /\ LET first == Head(Queue) IN
          \/ /\ first.type = "R"
             /\ Readers' = Readers \cup {first.proc}
             /\ Writers' = Writers
          \/ /\ first.type = "W"
             /\ Readers = {}
             /\ Writers' = {first.proc}
             /\ Readers' = Readers
    /\ Queue' = Tail(Queue)

Stop(p) ==
    \/ /\ p \in Readers
       /\ Readers' = Readers \ {p}
       /\ Writers' = Writers
       /\ Queue'   = Queue
    \/ /\ p \in Writers
       /\ Writers' = {}
       /\ Readers' = Readers
       /\ Queue'   = Queue

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in n : RequestRead(p)
    \/ \E p \in n : RequestWrite(p)
    \/ Begin
    \/ \E p \in n : Stop(p)

\* ----------------------------------------------------------------------
\* Fairness assumptions (weak fairness on all actions)
\* ----------------------------------------------------------------------
Fairness ==
    /\ WF_vars(\E p \in n : RequestRead(p))
    /\ WF_vars(\E p \in n : RequestWrite(p))
    /\ WF_vars(Begin)
    /\ WF_vars(\E p \in n : Stop(p))

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ Fairness

\* ----------------------------------------------------------------------
\* Type invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Cardinality(Writers) <= 1
    /\ Queue \in Seq(Req)
    /\ \A i \in DOMAIN Queue :
          /\ Queue[i].proc \in n
          /\ Queue[i].type \in {"R","W"}

\* ----------------------------------------------------------------------
\* Safety property
\* ----------------------------------------------------------------------
Safety ==
    /\ ~(Writers # {} /\ Readers # {})
    /\ Cardinality(Writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Liveness ==
    \A p \in n :
        /\ <> (p \in Readers)          \* every process eventually reads
        /\ <> (p \in Writers)          \* every process eventually writes
        /\ [] ( (p \in Readers) => <> (p \notin Readers) )  \* readers eventually stop
        /\ [] ( (p \in Writers) => <> (p \notin Writers) )  \* writers eventually stop

====