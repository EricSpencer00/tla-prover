---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* ----------------------------------------------------------------------
\* Derived set of actor identifiers (used throughout the spec)
\* The cfg file substitutes the identifier `n` for `NumActors`.
\* ----------------------------------------------------------------------
n == 1 .. NumActors
Actors == n

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Req == [proc : Actors, type : {"read", "write"}]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

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
    /\ p \in Actors
    /\ p \notin readers
    /\ p \notin writers
    /\ ~(\E i \in DOMAIN queue :
           queue[i].proc = p /\ queue[i].type = "read")
    /\ queue' = queue \o <<[proc |-> p, type |-> "read"]>>
    /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
    /\ p \in Actors
    /\ p \notin readers
    /\ p \notin writers
    /\ ~(\E i \in DOMAIN queue :
           queue[i].proc = p /\ queue[i].type = "write")
    /\ queue' = queue \o <<[proc |-> p, type |-> "write"]>>
    /\ UNCHANGED <<readers, writers>>

BeginAction ==
    /\ queue # <<>>
    /\ writers = {}               \* no writer currently active
    /\ LET front == Head(queue) IN
          \/ /\ front.type = "read"
             /\ readers' = readers \cup {front.proc}
             /\ writers' = writers
          \/ /\ front.type = "write"
             /\ readers = {}
             /\ readers' = readers
             /\ writers' = {front.proc}
    /\ queue' = Tail(queue)
    /\ UNCHANGED <<>>

StopRead(p) ==
    /\ p \in readers
    /\ readers' = readers \ {p}
    /\ UNCHANGED <<writers, queue>>

StopWrite(p) ==
    /\ p \in writers
    /\ writers' = {}
    /\ UNCHANGED <<readers, queue>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Actors : RequestRead(p)
    \/ \E p \in Actors : RequestWrite(p)
    \/ BeginAction
    \/ \E p \in Actors : StopRead(p)
    \/ \E p \in Actors : StopWrite(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\
    [][Next]_vars /\
    (\A p \in Actors : WF_vars(RequestRead(p))) /\
    (\A p \in Actors : WF_vars(RequestWrite(p))) /\
    WF_vars(BeginAction) /\
    (\A p \in Actors : WF_vars(StopRead(p))) /\
    (\A p \in Actors : WF_vars(StopWrite(p)))

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ queue \in Seq(Req)

\* ----------------------------------------------------------------------
\* Safety properties
\*   1. Readers and writers are never active together.
\*   2. At most one writer active.
\* ----------------------------------------------------------------------
Safety ==
    /\ (writers = {} \/ readers = {})
    /\ Cardinality(writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness property (fairness and progress)
\* ----------------------------------------------------------------------
Liveness ==
    /\ \A p \in Actors : []<>(p \in readers)      \* each process reads infinitely often
    /\ \A p \in Actors : []<>(p \in writers)      \* each process writes infinitely often
    /\ \A p \in Actors : []<>(p \notin readers)   \* readers eventually stop
    /\ \A p \in Actors : []<>(p \notin writers)   \* writers eventually stop

====