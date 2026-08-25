---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

\* Define the finite set of actor identifiers
n == 1 .. NumActors

\* Type of a request in the queue
Req == [proc : n, kind : {"Read", "Write"}]

VARIABLES Readers, Writers, Queue

\* ----------------------------------------------------------------------
\* State predicates
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers  \subseteq n
    /\ Queue \in Seq(Req)

Safety ==
    /\ (Writers = {} \/ Readers = {})
    /\ Cardinality(Writers) <= 1

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
ReqRead ==
    \E p \in n :
        /\ p \notin Readers
        /\ p \notin Writers
        /\ ~(\E q \in Queue : q.proc = p /\ q.kind = "Read")
        /\ Readers' = Readers
        /\ Writers'  = Writers
        /\ Queue'    = Append(Queue, [proc |-> p, kind |-> "Read"])

ReqWrite ==
    \E p \in n :
        /\ p \notin Readers
        /\ p \notin Writers
        /\ ~(\E q \in Queue : q.proc = p /\ q.kind = "Write")
        /\ Readers' = Readers
        /\ Writers'  = Writers
        /\ Queue'    = Append(Queue, [proc |-> p, kind |-> "Write"])

ProcessQueue ==
    /\ Queue # << >>
    /\ Writers = {}
    /\ LET first == Head(Queue) IN
         \/ /\ first.kind = "Read"
            /\ Readers' = Readers \cup {first.proc}
            /\ Writers'  = Writers
            /\ Queue'    = Tail(Queue)
         \/ /\ first.kind = "Write"
            /\ Readers = {}
            /\ Readers' = Readers
            /\ Writers'  = Writers \cup {first.proc}
            /\ Queue'    = Tail(Queue)

StopAct ==
    \E p \in n :
        /\ (p \in Readers) \/ (p \in Writers)
        /\ IF p \in Readers THEN
               /\ Readers' = Readers \ {p}
               /\ Writers' = Writers
           ELSE
               /\ Readers' = Readers
               /\ Writers' = Writers \ {p}
        /\ Queue' = Queue

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == \/ ReqRead \/ ReqWrite \/ ProcessQueue \/ StopAct

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == << Readers, Writers, Queue >>

Spec ==
    Init /\ [][Next]_vars
        /\ WF_vars(ReqRead)
        /\ WF_vars(ReqWrite)
        /\ WF_vars(ProcessQueue)
        /\ WF_vars(StopAct)

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Liveness ==
    /\ \A p \in n : []<>(p \in Readers)
    /\ \A p \in n : []<>(p \in Writers)
    /\ \A p \in n : [] (p \in Readers => <> (p \notin Readers))
    /\ \A p \in n : [] (p \in Writers => <> (p \notin Writers))

====