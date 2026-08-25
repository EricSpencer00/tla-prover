---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors
\* ``n'' will be substituted by the .cfg file; we give a default definition.
n == 1..NumActors

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES readers, writers, queue

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc == n

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ readers \subseteq Proc
    /\ writers \subseteq Proc
    /\ readers \cap writers = {}
    /\ queue \in Seq([type : {"read","write"}, proc : Proc])

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = <<>>

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
RequestRead(p) ==
    /\ p \in Proc
    /\ p \notin readers
    /\ p \notin writers
    /\ p \notin { q.proc : q \in queue }
    /\ queue' = Append(queue, [type |-> "read", proc |-> p])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
    /\ p \in Proc
    /\ p \notin readers
    /\ p \notin writers
    /\ p \notin { q.proc : q in queue }
    /\ queue' = Append(queue, [type |-> "write", proc |-> p])
    /\ UNCHANGED <<readers, writers>>

StartRead ==
    /\ queue # <<>>
    /\ writers = {}
    /\ Head(queue).type = "read"
    /\ readers' = readers \cup {Head(queue).proc}
    /\ writers' = writers
    /\ queue'   = Tail(queue)

StartWrite ==
    /\ queue # <<>>
    /\ writers = {}
    /\ Head(queue).type = "write"
    /\ readers = {}
    /\ writers' = writers \cup {Head(queue).proc}
    /\ readers' = readers
    /\ queue'   = Tail(queue)

Stop(p) ==
    /\ p \in Proc
    /\ (p \in readers \/ p \in writers)
    /\ readers' = readers \ {p}
    /\ writers' = writers \ {p}
    /\ UNCHANGED queue

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : RequestRead(p)
    \/ \E p \in Proc : RequestWrite(p)
    \/ StartRead
    \/ StartWrite
    \/ \E p \in Proc : Stop(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<readers, writers, queue>> /\ WF_<<readers, writers, queue>>(Next)

\* ----------------------------------------------------------------------
\* Safety invariant (combined safety property)
\* ----------------------------------------------------------------------
Safety ==
    /\ writers = {} \/ readers = {}
    /\ Cardinality(writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Liveness ==
    \A p \in Proc :
        /\ [] (p \in readers => <> (p \notin readers))
        /\ [] (p \in writers => <> (p \notin writers))
        /\ <> (p \in readers)
        /\ <> (p \in writers)

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
INVARIANTS == TypeOK /\ Safety
PROPERTIES == Liveness

====