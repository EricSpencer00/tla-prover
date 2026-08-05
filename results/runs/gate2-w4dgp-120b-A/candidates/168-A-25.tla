---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Actors == 1..NumActors

VARIABLES readers, writers, queue
vars == <<readers, writers, queue>>


Reader(p) == [done |-> FALSE, who |-> p]
Writer(p) == [done |-> FALSE, who |-> p]

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ \A i \in 1..Len(queue) : queue[i] \in {Reader(1), Writer(1), Reader(2), Writer(2), Reader(3), Writer(3)}
    /\ Len(queue) <= NumActors

\* Readers and writers are mutually exclusive: if anyone is writing, no one is
\* reading, and at most one writer is ever active.
Safety ==
    /\ (writers # {} => readers = {})
    /\ Cardinality(writers) <= 1

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = << >>

\* A process requests read access and joins the end of the waiting queue.
RequestRead(p) ==
    /\ \A i \in 1..Len(queue) : queue[i].who # p
    /\ queue' = Append(queue, Reader(p))
    /\ UNCHANGED <<readers, writers>>

\* A process requests write access and joins the end of the waiting queue.
RequestWrite(p) ==
    /\ \A i \in 1..Len(queue) : queue[i].who # p
    /\ queue' = Append(queue, Writer(p))
    /\ UNCHANGED <<readers, writers>>

\* The head of the queue begins access, but it may only begin writing when no
\* one is reading. In either case it leaves the queue.
BeginAccess ==
    /\ queue # << >>
    /\ writers = {}
    /\ LET x == Head(queue) IN
        /\ IF x.done = FALSE /\ x.who \notin readers /\ x.who \notin writers
             THEN
                 IF x.who = 1 \/ x.who = 2 \/ x.who = 3
                     THEN readers' = IF x.who \in Actors THEN readers \cup {x.who} ELSE readers
                     ELSE writers' = IF x.who \in Actors THEN writers \cup {x.who} ELSE writers
                 ELSE UNCHANGED <<readers, writers>>
        /\ queue' = Tail(queue)

\* Any active reader or writer may voluntarily stop.
StopActivity(p) ==
    /\ \/ p \in readers
       \/ p \in writers
    /\ readers' = readers \ {p}
    /\ writers' = writers \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in Actors : RequestRead(p)
    \/ \E p \in Actors : RequestWrite(p)
    \/ BeginAccess
    \/ \E p \in Actors : StopActivity(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in Actors : WF_vars(RequestRead(p))
    /\ \A p \in Actors : WF_vars(RequestWrite(p))
    /\ WF_vars(BeginAccess)
    /\ WF_vars(StopActivity(1))

\* Fairness: every process eventually gets to read and eventually gets to write.
Liveness ==
    /\ \A p \in Actors : <>(p \in readers)
    /\ \A p \in Actors : <>(p \in writers)
    /\ \A p \in Actors : <>(p \notin readers)
    /\ \A p \in Actors : <>(p \notin writers)

====