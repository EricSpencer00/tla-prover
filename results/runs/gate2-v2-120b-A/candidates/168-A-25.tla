---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, TLC

CONSTANT NumActors

VARIABLES readers, writers, queue

(*--algorithm ReadersWriters
variables readers = {}, writers = {}, queue = <<>>;

end algorithm;*)

\* ----------------------------------------------------------------------
\* State definitions
\* ----------------------------------------------------------------------
ReaderSet == { i \in 1..NumActors }
Request == [type : {"Read","Write"}, proc : ReaderSet]

\* The combined state as a tuple (for invariants)
vars == << readers, writers, queue >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue   = <<>>

\* ----------------------------------------------------------------------
\* Helper predicates
\* ----------------------------------------------------------------------
IsQueued(p) == \E i \in 1..Len(queue) : queue[i].proc = p

NoActiveWriter == writers = {}
NoActiveReaders == readers = {}

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
RequestRead(p) ==
    /\ p \in ReaderSet
    /\ ~IsQueued(p)
    /\ queue' = queue \o <<[type |-> "Read", proc |-> p]>>
    /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
    /\ p \in ReaderSet
    /\ ~IsQueued(p)
    /\ queue' = queue \o <<[type |-> "Write", proc |-> p]>>
    /\ UNCHANGED <<readers, writers>>

BeginOp ==
    /\ Len(queue) > 0
    /\ LET front == queue[1] IN
       IF front.type = "Read" THEN
          /\ NoActiveWriter
          /\ readers' = readers \cup {front.proc}
          /\ writers' = writers
          /\ queue'   = Tail(queue)
       ELSE
          /\ NoActiveWriter /\ NoActiveReaders
          /\ writers' = writers \cup {front.proc}
          /\ readers' = readers
          /\ queue'   = Tail(queue)
    /\ UNCHANGED queue

Stop(p) ==
    /\ (p \in readers \/ p \in writers)
    /\ readers' = readers \ {p}
    /\ writers' = writers \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in ReaderSet : RequestRead(p)
    \/ \E p \in ReaderSet : RequestWrite(p)
    \/ BeginOp
    \/ \E p \in ReaderSet : Stop(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant (optional but useful)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ readers \subseteq ReaderSet
    /\ writers \subseteq ReaderSet
    /\ writers \subseteq {} \/ (writers = {w} /\ w \in ReaderSet) \* at most one writer
    /\ \A i \in 1..Len(queue) : queue[i] \in Request

\* ----------------------------------------------------------------------
\* Safety invariant
\* ----------------------------------------------------------------------
Safety ==
    /\ (writers = {} => readers \subseteq ReaderSet)
    /\ (writers # {} => readers = {})
    /\ Cardinality(writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness property (placeholder; model checker may need a concrete formula)
\* ----------------------------------------------------------------------
Liveness == <> (TRUE)

====