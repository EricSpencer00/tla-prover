---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\* Types and derived sets
\* ----------------------------------------------------------------------
Proc == 1..NumActors

ReqType == {"Read", "Write"}

VARIABLES readers, writer, queue

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* A request is a record containing its type and the process that made it
Req == [type : ReqType, proc : Proc]

\* Action identifiers required for model checking
vars == << readers, writer, queue >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ readers = {}
    /\ writer  = {}
    /\ queue   = << >>

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
RequestRead(p) ==
    /\ p \in Proc
    /\ ~\E r \in queue : r.type = "Read" /\ r.proc = p
    /\ queue' = queue \o << [type |-> "Read", proc |-> p] >>
    /\ UNCHANGED readers
    /\ UNCHANGED writer

RequestWrite(p) ==
    /\ p \in Proc
    /\ ~\E r \in queue : r.type = "Write" /\ r.proc = p
    /\ queue' = queue \o << [type |-> "Write", proc |-> p] >>
    /\ UNCHANGED readers
    /\ UNCHANGED writer

BeginOperation ==
    /\ Len(queue) > 0
    /\ LET front == Head(queue) IN
       /\ front.type = "Read"
          /\ writer = {}
          /\ readers' = readers \cup {front.proc}
          /\ queue'   = Tail(queue)
       \/ front.type = "Write"
          /\ readers = {}
          /\ writer'  = writer \cup {front.proc}
          /\ queue'   = Tail(queue)
    /\ UNCHANGED writer   \* when a read begins
    /\ UNCHANGED readers  \* when a write begins

Stop(p) ==
    /\ p \in Proc
    /\ (p \in readers => readers' = readers \ {p})
    /\ (p \in writer  => writer'  = writer  \ {p})
    /\ UNCHANGED queue
    /\ (p \notin readers /\ p \notin writer => UNCHANGED << readers, writer >>)

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : RequestRead(p)
    \/ \E p \in Proc : RequestWrite(p)
    \/ BeginOperation
    \/ \E p \in Proc : Stop(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ readers \subseteq Proc
    /\ writer  \subseteq Proc
    /\ writer \subseteq readers => FALSE   \* writer and readers must be disjoint
    /\ \A i \in 1..Len(queue) :
          /\ queue[i].type \in ReqType
          /\ queue[i].proc \in Proc

\* ----------------------------------------------------------------------
\* Safety invariant (captures the two safety conditions)
\* ----------------------------------------------------------------------
Safety ==
    /\ (writer = {} \/ readers = {})
    /\ Cardinality(writer) <= 1

\* ----------------------------------------------------------------------
\* Liveness properties
\* ----------------------------------------------------------------------
\* Every process eventually reads
ReadLiveness(p) == <> (p \in readers)

\* Every process eventually writes
WriteLiveness(p) == <> (p \in writer)

\* Every active reader eventually stops
ReadStops(p) == [] (p \in readers => <> (p \notin readers))

\* Every active writer eventually stops
WriteStops(p) == [] (p \in writer => <> (p \notin writer))

\* Combined liveness property required by the .cfg
Liveness == \A p \in Proc : (ReadLiveness(p) /\ WriteLiveness(p) /\ ReadStops(p) /\ WriteStops(p))

====