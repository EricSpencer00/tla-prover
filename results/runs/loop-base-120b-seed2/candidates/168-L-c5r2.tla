---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

\* Mapping NumActors to a concrete set of actor identifiers
Actors == 1 .. NumActors

\* Types of requests
RequestTypes == {"Read", "Write"}

\* State variables
VARIABLES readers, writers, q

\* ----------------------------------------------------------------------
\* Type invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ readers \cap writers = {}
    /\ q \in Seq([pid : Actors, typ : RequestTypes])

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Safety ==
    /\ Cardinality(writers) <= 1
    /\ (writers = {} \/ readers = {})

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ q = << >>

\* ----------------------------------------------------------------------
\* Auxiliary definitions
\* ----------------------------------------------------------------------
\* Append a request to the queue
AppendReq(req) ==
    Append(q, req)

\* Remove the first element of the queue
TailQ == Tail(q)

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* A process may request to read
RequestRead ==
    \E p \in Actors :
        /\ p \notin readers
        /\ p \notin writers
        /\ ~(\E i \in 1 .. Len(q) : q[i].pid = p)
        /\ readers' = readers
        /\ writers' = writers
        /\ q' = Append(q, [pid |-> p, typ |-> "Read"])

\* A process may request to write
RequestWrite ==
    \E p \in Actors :
        /\ p \notin readers
        /\ p \notin writers
        /\ ~(\E i \in 1 .. Len(q) : q[i].pid = p)
        /\ readers' = readers
        /\ writers' = writers
        /\ q' = Append(q, [pid |-> p, typ |-> "Write"])

\* The front request of the queue is processed
BeginProcessing ==
    /\ Len(q) > 0
    /\ LET front == q[1] IN
        /\ front.typ = "Read"
            => /\ writers = {}
               /\ readers' = readers \cup {front.pid}
               /\ writers' = writers
        /\ front.typ = "Write"
            => /\ readers = {}
               /\ writers' = writers \cup {front.pid}
               /\ readers' = readers
        /\ q' = Tail(q)

\* A process that is active may stop
StopActivity ==
    \E p \in Actors :
        \/ /\ p \in readers
           /\ readers' = readers \ {p}
           /\ writers' = writers
        \/ /\ p \in writers
           /\ writers' = writers \ {p}
           /\ readers' = readers
        /\ q' = q

\* The overall next-state relation
Next ==
    \/ RequestRead
    \/ RequestWrite
    \/ BeginProcessing
    \/ StopActivity

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<readers, writers, q>>
    /\ WF_<<readers, writers, q>>(RequestRead)
    /\ WF_<<readers, writers, q>>(RequestWrite)
    /\ WF_<<readers, writers, q>>(BeginProcessing)
    /\ WF_<<readers, writers, q>>(StopActivity)

\* ----------------------------------------------------------------------
\* Liveness property (fair access for every process)
\* ----------------------------------------------------------------------
Liveness ==
    \A p \in Actors : ( <> (p \in readers) /\ <> (p \in writers) )

====