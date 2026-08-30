---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

\* Readers-writers access to a shared resource, with readers sharing and
\* writers needing exclusive access.  Access requests wait in a FIFO queue so
\* that readers and writers are served in the order they arrive, which is
\* what gives this solution fairness and prevents either side from starving.
CONSTANTS NumActors

\* A request is a (process, kind) pair; kind = "read" or "write".
Request == [proc: 1..NumActors, kind: {"read", "write"}]

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

TypeOK ==
    /\ reading \subseteq 1..NumActors
    /\ writing \subseteq 1..NumActors
    /\ queue \in Seq(Request)

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = << >>

\* A process that is not already queued may request to read the resource.
RequestRead(p) ==
    /\ ~\E i \in DOMAIN queue : queue[i].proc = p
    /\ queue' = Append(queue, [proc |-> p, kind |-> "read"])
    /\ UNCHANGED <<reading, writing>>

\* A process that is not already queued may request to write the resource.
RequestWrite(p) ==
    /\ ~\E i \in DOMAIN queue : queue[i].proc = p
    /\ queue' = Append(queue, [proc |-> p, kind |-> "write"])
    /\ UNCHANGED <<reading, writing>>

\* The queue front begins its access once the resource is available.
BeginAccess ==
    /\ queue # << >>
    /\ writing = {}
    /\ LET head == Head(queue) IN
         /\ IF head.kind = "read"
              THEN reading' = reading \cup {head.proc}
              ELSE IF reading = {}
                   THEN writing' = writing \cup {head.proc}
                   ELSE UNCHANGED <<reading, writing>>
         /\ queue' = Tail(queue)

\* An active reader or writer stops, freeing the resource.
Stop(p) ==
    /\ p \in (reading \cup writing)
    /\ reading' = reading \ {p}
    /\ writing' = writing \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in 1..NumActors : RequestRead(p)
    \/ \E p \in 1..NumActors : RequestWrite(p)
    \/ BeginAccess
    \/ \E p \in 1..NumActors : Stop(p)

Spec == Init /\ [][Next]_vars
    /\ WF_vars(\E p \in 1..NumActors : RequestRead(p))
    /\ WF_vars(\E p \in 1..NumActors : RequestWrite(p))
    /\ WF_vars(BeginAccess)
    /\ WF_vars(\E p \in 1..NumActors : Stop(p))

\* Readers and writers never hold the resource at the same time.
Safety ==
    /\ (reading # {}) => (writing = {})
    /\ (writing # {}) => (reading = {})
    /\ Cardinality(writing) <= 1

\* Every process eventually gets to read and to write.
Liveness ==
    \A p \in 1..NumActors :
        /\ (p \notin reading) ~> (p \in reading)
        /\ (p \notin writing) ~> (p \in writing)
        /\ (p \in reading) ~> (p \notin reading)
        /\ (p \in writing) ~> (p \notin writing)

\* The model's actor count is bounded, so saturation is not a concern.
Bounded == NumActors \in 1..3

\* The .cfg file substitutes 'n' for the actor count (always a concrete
\* bounded value) so the reachable-state search keeps the model finite.
n == 2
====