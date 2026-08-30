---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Actors == 1..NumActors
Modes == {"read", "write"}

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

TypeOK ==
    /\ reading \subseteq Actors
    /\ writing \subseteq Actors
    /\ queue \in Seq[Actors \X Modes]

\* SAFETY: Readers and writers are mutually exclusive, and at most one writer
\* holds the resource at any time.
Safety == (reading # {}) => (writing = {}) /\ Cardinality(writing) <= 1

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = <<>>

RequestRead(p) ==
    /\ ~\E i \in DOMAIN queue : queue[i][1] = p /\ queue[i][2] = "read"
    /\ queue' = Append(queue, <<p, "read">>)
    /\ UNCHANGED <<reading, writing>>

RequestWrite(p) ==
    /\ ~\E i \in DOMAIN queue : queue[i][1] = p /\ queue[i][2] = "write"
    /\ queue' = Append(queue, <<p, "write">>)
    /\ UNCHANGED <<reading, writing>>

BeginService ==
    /\ Len(queue) > 0
    /\ writing = {}
    /\ LET p == Head(queue)[1] IN
       LET m == Head(queue)[2] IN
         /\ \/ (m = "read" /\ reading' = reading \cup {p} /\ queue' = Tail(queue))
            \/ (m = "write" /\ reading = {} /\ writing' = {p} /\ queue' = Tail(queue))
         /\ UNCHANGED <<>>

StopActivity(p) ==
    /\ (p \in reading \/ p \in writing)
    /\ reading' = reading \ {p}
    /\ writing' = writing \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in Actors : RequestRead(p)
    \/ \E p \in Actors : RequestWrite(p)
    \/ BeginService
    \/ \E p \in Actors : StopActivity(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(StopActivity(1))
    /\ WF_vars(StopActivity(2))
    /\ WF_vars(StopActivity(3))
    /\ WF_vars(BeginService)

\* LIVENESS: every actor eventually gets to act as a reader and as a writer.
Liveness == \A p \in Actors : ([]<>(p \in reading) /\ []<>(p \in writing))

====