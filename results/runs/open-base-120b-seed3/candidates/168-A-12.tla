---- MODULE ReadersWriters ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT NumActors

\* ----------------------------------------------------------------------
\* Set of actor identifiers
\* ----------------------------------------------------------------------
n == 1 .. NumActors

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Req == [proc : n, type : {"Read", "Write"}]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Readers, Writers, Queue

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Pending == { q.proc : q \in SeqToSet(Queue) }

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
    /\ p \notin Pending
    /\ Queue' = Queue ^ <<[proc |-> p, type |-> "Read"]>>
    /\ UNCHANGED <<Readers, Writers>>

RequestWrite(p) ==
    /\ p \in n
    /\ p \notin Readers
    /\ p \notin Writers
    /\ p \notin Pending
    /\ Queue' = Queue ^ <<[proc |-> p, type |-> "Write"]>>
    /\ UNCHANGED <<Readers, Writers>>

ProcessQueue ==
    /\ Queue # <<>>
    /\ Writers = {}
    /\ LET front == Head(Queue) IN
       IF front.type = "Read" THEN
          /\ Readers' = Readers \cup {front.proc}
          /\ Writers' = Writers
          /\ Queue'   = Tail(Queue)
       ELSE
          /\ Readers = {}
          /\ Writers' = {front.proc}
          /\ Queue'   = Tail(Queue)
    /\ UNCHANGED <<Readers, Writers>> \cup {Queue} \ {Readers', Writers', Queue'}

StopRead(p) ==
    /\ p \in Readers
    /\ Readers' = Readers \ {p}
    /\ UNCHANGED <<Writers, Queue>>

StopWrite(p) ==
    /\ p \in Writers
    /\ Writers' = {}
    /\ UNCHANGED <<Readers, Queue>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in n : RequestRead(p)
    \/ \E p \in n : RequestWrite(p)
    \/ ProcessQueue
    \/ \E p \in Readers : StopRead(p)
    \/ \E p \in Writers : StopWrite(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<Readers, Writers, Queue>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Readers \subseteq n
    /\ Writers \subseteq n
    /\ Cardinality(Writers) <= 1
    /\ Queue \in Seq(Req)

Safety ==
    /\ (Writers = {} \/ Readers = {})
    /\ Cardinality(Writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Liveness ==
    \A p \in n :
        <> (p \in Readers) /\ <> (p \in Writers)

====