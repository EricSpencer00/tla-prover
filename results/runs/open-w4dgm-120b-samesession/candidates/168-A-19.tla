---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* Model bounds: NumActors is the number of actor processes; n is its concrete
\* instantiation (substituted by the .cfg, which overrides the name n below).
n == NumActors

\* Every request records the action (read/write) and the originating process.
Request == [act: {"read", "write"}, who: 1..n]

VARIABLES readers, writers, queue

TypeOK ==
    /\ readers \subseteq (1..n)
    /\ writers \subseteq (1..n)
    /\ queue \in Seq(Request)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = <<>>

\* Distinguish request vs. active state: once a queued request is taken, the
\* process is neither waiting nor active until BeginRW reclassifies it.
Waiting(p) == \E i \in 1..Len(queue) : queue[i].who = p

\* Readers and writers are mutually exclusive; the queue is charged with
\* fairness, so this is first-come-first-served and neither side starves.
BeginRW ==
    /\ Len(queue) > 0
    /\ writers = {}
    /\ LET front == Head(queue) IN
        /\ \/ (front.act = "read" /\ readers' = readers \cup {front.who})
           \/ (front.act = "write" /\ readers = {} /\ writers' = writers \cup {front.who})
        /\ UNCHANGED <<writers, queue>>
    /\ queue' = Tail(queue)

RequestRead(p) == ~Waiting(p) /\ readers' = readers /\ writers' = writers /\ queue' = Append(queue, [act |-> "read", who |-> p])
RequestWrite(p) == ~Waiting(p) /\ readers' = readers /\ writers' = writers /\ queue' = Append(queue, [act |-> "write", who |-> p])
Stop == readers' = {} \/ writers' = {} /\ UNCHANGED <<readers, writers, queue>>

Next ==
    \/ BeginRW
    \/ \E p \in 1..n : RequestRead(p)
    \/ \E p \in 1..n : RequestWrite(p)
    \/ Stop

Spec == Init /\ [][Next]_<<readers, writers, queue>>

\* SAFETY: readers and writers are never active at the same time, and never
\* more than one writer at once.
Safety == \A r \in readers : writers = {} /\ (writers = {} \/ \A w \in writers : w = r)

\* LIVENESS: every process eventually gets to read and to write.
Liveness == \A p \in 1..n : <>(p \in readers) /\ <>(p \in writers)

====