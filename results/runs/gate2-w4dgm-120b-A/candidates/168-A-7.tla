---- MODULE ReadersWriters ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS NumActors

\* A request is a (type, actor) pair; the queue is a sequence of them.
Request == [kind: {"read", "write"}, p: 1..n]

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

TypeOK ==
    /\ readers \subseteq (1..n)
    /\ writers \subseteq (1..n)
    /\ queue \in Seq(Request)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = << >>

RequestRead(p) ==
    /\ \A i \in DOMAIN queue : queue[i].p # p
    /\ queue' = Append(queue, [kind |-> "read", p |-> p])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
    /\ \A i \in DOMAIN queue : queue[i].p # p
    /\ queue' = Append(queue, [kind |-> "write", p |-> p])
    /\ UNCHANGED <<readers, writers>>

\* The queue is processed head-first; a write waits for an empty reader set.
BeginAccess ==
    /\ queue # << >>
    /\ writers = {}
    /\ LET r == Head(queue) IN
        IF r.kind = "read" THEN
            /\ readers' = readers \cup {r.p}
            /\ writers' = writers
            /\ queue' = Tail(queue)
        ELSE
            /\ readers = {}
            /\ readers' = readers
            /\ writers' = writers \cup {r.p}
            /\ queue' = Tail(queue)

StopActivity(p) ==
    /\ p \in readers \/ p \in writers
    /\ readers' = readers \ {p}
    /\ writers' = writers \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in 1..n : RequestRead(p)
    \/ \E p \in 1..n : RequestWrite(p)
    \/ BeginAccess
    \/ \E p \in 1..n : StopActivity(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(BeginAccess)
    /\ \A p \in 1..n : WF_vars(StopActivity(p))

Safety ==
    /\ ~(~(readers = {}) /\ ~ (writers = {}))
    /\ writers \subseteq (1..n)

Liveness ==
    /\ (\A p \in 1..n : (p \in readers) ~> (p \notin readers))
    /\ (\A p \in 1..n : (p \in writers) ~> (p \notin writers))

\* The queue capacity is bounded by the actor count: with that many requests enqueued, every actor has a pending request, and no further one is admitted.
BoundedQueue == Len(queue) <= n
====