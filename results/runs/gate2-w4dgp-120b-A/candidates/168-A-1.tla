---- MODULE ReadersWriters ----
\* Readers and writers share one resource under a fair first-come-first-served queue.
\* Readers may proceed concurrently, but as a writer commits exclusive access it blocks
\* all readers. Every process eventually gets to read and to write, and readers and
\* writers are never active at the same time.
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Actors == 1 .. NumActors
Modes == {"read", "write"}
Req == [proc : Actors, mode : Modes]

VARIABLES reading, writing, queue

TypeOK ==
    /\ reading \in SUBSET Actors
    /\ writing \in SUBSET Actors
    /\ queue \in Seq(Req)

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = << >>

RequestRead(p) ==
    /\ \A i \in 1 .. Len(queue) : queue[i].proc # p \/ queue[i].mode # "read"
    /\ queue' = Append(queue, [proc |-> p, mode |-> "read"])
    /\ UNCHANGED <<reading, writing>>

RequestWrite(p) ==
    /\ \A i \in 1 .. Len(queue) : queue[i].proc # p \/ queue[i].mode # "write"
    /\ queue' = Append(queue, [proc |-> p, mode |-> "write"])
    /\ UNCHANGED <<reading, writing>>

BeginAccess ==
    /\ Len(queue) > 0
    /\ writing = {}
    /\ LET r == Head(queue) IN
        /\ queue' = Tail(queue)
        /\ IF r.mode = "read"
            THEN reading' = reading \cup {r.proc}
                 /\ writing' = {}
            ELSE IF reading = {}
                THEN writing' = writing \cup {r.proc}
                     /\ reading' = {}
                ELSE reading' = reading
                     /\ writing' = writing
    /\ UNCHANGED queue

StopActivity(p) ==
    /\ (p \in reading \/ p \in writing)
    /\ reading' = reading \ {p}
    /\ writing' = writing \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in Actors : RequestRead(p)
    \/ \E p \in Actors : RequestWrite(p)
    \/ BeginAccess
    \/ \E p \in Actors : StopActivity(p)

Spec ==
    /\ Init
    /\ [][Next]_<<reading, writing, queue>>
    /\ WF_vars(\E p \in Actors : RequestRead(p))
    /\ WF_vars(\E p \in Actors : RequestWrite(p))
    /\ WF_vars(BeginAccess)
    /\ WF_vars(\E p \in Actors : StopActivity(p))

Safety ==
    /\ (writing # {} => reading = {})
    /\ (reading # {} => writing = {})
    /\ Cardinality(writing) <= 1

Liveness ==
    /\ \A p \in Actors : (p \in reading) ~> (p \notin reading)
    /\ \A p \in Actors : (p \in writing) ~> (p \notin writing)

====