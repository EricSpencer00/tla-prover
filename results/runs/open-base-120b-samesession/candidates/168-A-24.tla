---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\*  The set of actor identifiers (substituted in the .cfg file)
\* ----------------------------------------------------------------------
n == 1..NumActors

\* ----------------------------------------------------------------------
\*  State variables
\* ----------------------------------------------------------------------
VARIABLES Readers, Writers, Queue

\* ----------------------------------------------------------------------
\*  Types
\* ----------------------------------------------------------------------
Request == [proc : n, typ : {"Read", "Write"}]

TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Disjoint[Readers, Writers]
    /\ Cardinality(Writers) <= 1
    /\ Queue \in Seq(Request)

\* ----------------------------------------------------------------------
\*  Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Readers = {}
    /\ Writers = {}
    /\ Queue   = <<>>

\* ----------------------------------------------------------------------
\*  Actions
\* ----------------------------------------------------------------------
RequestRead(p) ==
    /\ p \in n
    /\ ~(\E q \in Queue : q.proc = p /\ q.typ = "Read")
    /\ Queue' = Queue \o <<[proc |-> p, typ |-> "Read"]>>
    /\ UNCHANGED <<Readers, Writers>>

RequestWrite(p) ==
    /\ p \in n
    /\ ~(\E q \in Queue : q.proc = p /\ q.typ = "Write")
    /\ Queue' = Queue \o <<[proc |-> p, typ |-> "Write"]>>
    /\ UNCHANGED <<Readers, Writers>>

ProcessQueue ==
    /\ Queue # <<>>
    /\ LET front == Head(Queue) IN
       /\ Writers = {}
       /\ IF front.typ = "Read" THEN
            /\ Readers' = Readers \cup {front.proc}
            /\ Writers' = Writers
            /\ Queue'   = Tail(Queue)
          ELSE
            /\ Readers = {}               \* no readers while a write may start
            /\ Writers' = {front.proc}
            /\ Readers' = Readers
            /\ Queue'   = Tail(Queue)
    /\ UNCHANGED [][Readers, Writers, Queue] \* (no other vars)

Stop(p) ==
    /\ p \in n
    /\ \/ p \in Readers
          /\ Readers' = Readers \ {p}
          /\ Writers' = Writers
       \/ p \in Writers
          /\ Writers' = Writers \ {p}
          /\ Readers' = Readers
    /\ UNCHANGED Queue

\* ----------------------------------------------------------------------
\*  Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in n : RequestRead(p)
    \/ \E p \in n : RequestWrite(p)
    \/ ProcessQueue
    \/ \E p \in n : Stop(p)

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<Readers, Writers, Queue>>
    /\ WF_<<Readers, Writers, Queue>>( \E p \in n : RequestRead(p) )
    /\ WF_<<Readers, Writers, Queue>>( \E p \in n : RequestWrite(p) )
    /\ WF_<<Readers, Writers, Queue>>( ProcessQueue )
    /\ WF_<<Readers, Writers, Queue>>( \E p \in n : Stop(p) )

\* ----------------------------------------------------------------------
\*  Safety property (readers and writers never active together,
\*  at most one writer)
\* ----------------------------------------------------------------------
Safety ==
    /\ Disjoint[Readers, Writers]
    /\ Cardinality(Writers) <= 1

\* ----------------------------------------------------------------------
\*  Liveness property (no starvation, activity eventually stops)
\* ----------------------------------------------------------------------
Liveness ==
    /\ \A p \in n :
         ( <> (p \in Readers) )            \* every process eventually reads
         /\ ( <> (p \in Writers) )         \* every process eventually writes
         /\ ( [] (p \in Readers => <> (p \notin Readers)) )
         /\ ( [] (p \in Writers => <> (p \notin Writers)) )

\* ----------------------------------------------------------------------
\*  Invariants required by the .cfg file
\* ----------------------------------------------------------------------
THEOREM TypeOKInvariant == Spec => []TypeOK
THEOREM SafetyInvariant == Spec => []Safety

\* ----------------------------------------------------------------------
\*  Property required by the .cfg file
\* ----------------------------------------------------------------------
THEOREM LivenessProperty == Spec => Liveness

=============================================================================