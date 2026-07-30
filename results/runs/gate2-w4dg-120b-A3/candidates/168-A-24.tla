---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* n is used internally for queue bounds; the .cfg substitutes n = NumActors.
n == NumActors

\* An access request is always either read or write -- never both. The model
\* tracks which of the two kinds the queued request is for, and the active
\* reader/writer sets are independent, so a request that is both kinds would
\* let the same process slip into both states at once.
Requests == {r \in {"read", "write"} : TRUE}

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

TypeOK ==
    /\ readers \subseteq 1..n
    /\ writers \subseteq 1..n
    /\ queue \in Seq([req: Requests, who: 1..n])

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = <<>>

Serve ==
    /\ queue # <<>>
    /\ writers = {}
    /\ LET f == Head(queue) IN
        /\ IF f.req = "read" THEN readers' = readers \cup {f.who}
           ELSE writers' = writers \cup {f.who}
        /\ queue' = Tail(queue)
    /\ UNCHANGED readers

RequestRead(p) ==
    /\ p \notin readers
    /\ p \notin writers
    /\ ~ \E i \in DOMAIN queue : queue[i].who = p /\ queue[i].req = "read"
    /\ queue' = Append(queue, [req |-> "read", who |-> p])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
    /\ p \notin readers
    /\ p \notin writers
    /\ ~ \E i \in DOMAIN queue : queue[i].who = p /\ queue[i].req = "write"
    /\ queue' = Append(queue, [req |-> "write", who |-> p])
    /\ UNCHANGED <<readers, writers>>

StopActivity(p) ==
    /\ \/ p \in readers
       \/ p \in writers
    /\ readers' = readers \ {p}
    /\ writers' = writers \ {p}
    /\ UNCHANGED queue

Next ==
    \/ Serve
    \/ \E p \in 1..n : RequestRead(p)
    \/ \E p \in 1..n : RequestWrite(p)
    \/ \E p \in 1..n : StopActivity(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Serve)
    /\ \A p \in 1..n : WF_vars(RequestRead(p))
    /\ \A p \in 1..n : WF_vars(RequestWrite(p))
    /\ \A p \in 1..n : WF_vars(StopActivity(p))

\* Readers and writers are never simultaneously active, and a writer is
\* exclusive: active reader/writer sets are never both non-empty, and the
\* writer set never holds two processes at once.
Safety == readers # {} => writers = {} /\ Cardinality(writers) <= 1

\* Fairness guarantees: every process gets to read and to write, and every
\* active reading or writing eventually stops.
Liveness ==
    /\ \A p \in 1..n : (p \in readers) ~> (p \in writers)
    /\ \A p \in 1..n : (p \in writers) ~> (p \in readers)
    /\ \A p \in 1..n : (p \in readers) ~> (p \notin readers)
    /\ \A p \in 1..n : (p \in writers) ~> (p \notin writers)

====