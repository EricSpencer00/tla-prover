---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* An empty sequence literal ends in \infty instead of the integer 0, so the
\* empty-sequence test below uses SeqLen rather than Len.
VARIABLES readers, writers, queue

vars == << readers, writers, queue >>

Requests == [pr : NumActors, kind : {"r", "w"}]

TypeOK ==
    /\ readers \subseteq NumActors
    /\ writers \subseteq NumActors
    /\ queue \in Seq(Requests)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = << >>

\* A process that is not already waiting to read joins the end of the queue.
RequestRead(p) ==
    /\ \A i \in 1..SeqLen(queue) : queue[i].pr # p
    /\ queue' = Append(queue, [pr |-> p, kind |-> "r"])
    /\ UNCHANGED << readers, writers >>

\* A process that is not already waiting to write joins the end of the queue.
RequestWrite(p) ==
    /\ \A i \in 1..SeqLen(queue) : queue[i].pr # p
    /\ queue' = Append(queue, [pr |-> p, kind |-> "w"])
    /\ UNCHANGED << readers, writers >>

\* Because readers and writers are exclusive, the front request is granted only
\* when its kind's counterpart is empty.
BeginService ==
    /\ queue # << >>
    /\ writers = {}
    /\ LET front == Head(queue) IN
        /\ \/ front.kind = "r"
           \/ /\ front.kind = "w"
              /\ readers = {}
        /\ IF front.kind = "r" THEN readers' = readers \cup {front.pr} ELSE readers' = readers
        /\ IF front.kind = "w" THEN writers' = writers \cup {front.pr} ELSE writers' = writers
    /\ queue' = Tail(queue)

StopActivity(p) ==
    /\ readers' = readers \ {p}
    /\ writers' = writers \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in NumActors : RequestRead(p)
    \/ \E p \in NumActors : RequestWrite(p)
    \/ BeginService
    \/ \E p \in NumActors : StopActivity(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in NumActors : RequestRead(p))
    /\ WF_vars(\E p \in NumActors : RequestWrite(p))
    /\ WF_vars(BeginService)
    /\ \A p \in NumActors : SF_vars(StopActivity(p))

\* Readers and writers are never simultaneously active.  Also, at most one
\* writer is ever active.
Safety ==
    /\ writers = {} \/ readers = {}
    /\ writers \subseteq NumActors
    /\ Cardinality(writers) <= 1

\* Every process eventually gets to read and to write; fairness on the
\* BeginService and StopActivity actions is what makes this real progress.
Liveness ==
    /\ \A p \in NumActors : (p \notin readers) ~> (p \in readers)
    /\ \A p \in NumActors : (p \notin writers) ~> (p \in writers)
    /\ \A p \in NumActors : (p \in readers) ~> (p \notin readers)
    /\ \A p \in NumActors : (p \in writers) ~> (p \notin writers)

\* The model's actor set can be instantiated as any non-empty finite set;
\* the shape of the queue is what keeps the system from starving anyone.
n == 1..3

====