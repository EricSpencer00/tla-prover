---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

\* Set of actor identifiers (to be instantiated in the .cfg file)
n == 1 .. NumActors

VARIABLES Readers, Writers, Queue

\*=====================================================================
\* Helper definitions
\*=====================================================================
PendingProcs == { q.proc : q \in Queue }

\*=====================================================================
\* Initial state
\*=====================================================================
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = << >>

\*=====================================================================
\* Actions
\*=====================================================================
ReadReq ==
    \E p \in n :
        /\ p \notin Readers
        /\ p \notin Writers
        /\ p \notin PendingProcs
        /\ Queue' = Append(Queue, [proc |-> p, type |-> "read"])
        /\ UNCHANGED << Readers, Writers >>

WriteReq ==
    \E p \in n :
        /\ p \notin Readers
        /\ p \notin Writers
        /\ p \notin PendingProcs
        /\ Queue' = Append(Queue, [proc |-> p, type |-> "write"])
        /\ UNCHANGED << Readers, Writers >>

Process ==
    /\ Queue # << >>
    /\ Writers = {}
    /\ 
       ( /\ Queue[1].type = "read"
          /\ Readers' = Readers \cup { Queue[1].proc }
          /\ Writers' = Writers
          /\ Queue'   = Tail(Queue)
       )
       \/ 
       ( /\ Queue[1].type = "write"
          /\ Readers = {}
          /\ Writers' = Writers \cup { Queue[1].proc }
          /\ Readers' = Readers
          /\ Queue'   = Tail(Queue)
       )
    /\ UNCHANGED << >>

StopAct ==
    \E p \in n :
        /\ p \in Readers \/ p \in Writers
        /\ IF p \in Readers
              THEN Readers' = Readers \ {p}
                   /\ Writers' = Writers
           ELSE Readers' = Readers
                /\ Writers' = Writers \ {p}
        /\ UNCHANGED << Queue >>

Next ==
    \/ ReadReq
    \/ WriteReq
    \/ Process
    \/ StopAct

\*=====================================================================
\* Specification
\*=====================================================================
Spec ==
    Init /\ [][Next]_<< Readers, Writers, Queue >>
          /\ WF_vars(ReadReq)
          /\ WF_vars(WriteReq)
          /\ WF_vars(Process)
          /\ WF_vars(StopAct)

\*=====================================================================
\* Invariant: type correctness
\*=====================================================================
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ DISJOINT(Readers, Writers)
    /\ Queue \in Seq([proc : n, type : {"read","write"}])

\*=====================================================================
\* Safety property
\*=====================================================================
Safety ==
    /\ (Writers = {} \/ Readers = {})
    /\ \A w1 \in Writers : \A w2 \in Writers : w1 = w2

\*=====================================================================
\* Liveness property
\*=====================================================================
Liveness ==
    \A p \in n :
        (<> (p \in Readers)               /\   <> (p \in Writers))
        /\ ([] (p \in Readers => <> (p \notin Readers)))
        /\ ([] (p \in Writers => <> (p \notin Writers)))

=============================================================================