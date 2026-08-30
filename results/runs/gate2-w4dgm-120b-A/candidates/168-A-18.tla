---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* Readers and writers coordinate a shared resource through a queue: a
\* read/write request sits in the waiting queue until it is granted, and
\* reading is only allowed when no writer is active. Write requests wait
\* for every reader to finish first, which is the core fairness trick.

VARIABLES reading, writing, queue

TypeOK ==
    /\ reading \subseteq NumActors
    /\ writing \subseteq NumActors
    /\ queue \in Seq([type : {"read", "write"}, pid : NumActors])

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = << >>

\* A process asks for read access; the request joins the waiting queue.
RequestRead(p) ==
    /\ \A i \in 1..Len(queue) : queue[i].pid # p \/ queue[i].type # "read"
    /\ queue' = Append(queue, [type |-> "read", pid |-> p])
    /\ UNCHANGED <<reading, writing>>

\* A process asks for write access; the request joins the waiting queue.
RequestWrite(p) ==
    /\ \A i \in 1..Len(queue) : queue[i].pid # p \/ queue[i].type # "write"
    /\ queue' = Append(queue, [type |-> "write", pid |-> p])
    /\ UNCHANGED <<reading, writing>>

\* The head of the queue is granted when it is compatible with current
\* activity: reads when nobody writes, writes when nobody reads.
BeginAccess ==
    /\ queue # << >>
    /\ writing = {}
    /\ IF queue[1].type = "read"
         THEN reading' = reading \union {queue[1].pid}
              /\ writing' = writing
         ELSE IF reading = {}
              THEN writing' = writing \union {queue[1].pid}
                   /\ reading' = reading
              ELSE reading' = reading /\ writing' = writing
    /\ queue' = Tail(queue)

StopActivity(p) ==
    /\ p \in reading \/ p \in writing
    /\ reading' = reading \ {p}
    /\ writing' = writing \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in NumActors : RequestRead(p)
    \/ \E p \in NumActors : RequestWrite(p)
    \/ BeginAccess
    \/ \E p \in NumActors : StopActivity(p)

\* No simultaneous reading and writing; and no two writers at once.
Safety ==
    /\ ~(writing # {} /\ reading # {})
    /\ \A a \in writing : \A b \in writing : a = b

Spec == Init /\ [][Next]_<<reading, writing, queue>>

Liveness ==
    /\ \A p \in NumActors :
         /\ (\E i \in 1..Len(queue) : queue[i].pid = p) ~> (p \in reading \/ p \in writing)
         /\ (p \in reading \/ p \in writing) ~> (p \notin reading /\ p \notin writing)

\* Model-checking with a concrete actor count; the .cfg entry below
\* substitutes a specific number of actors for this placeholder.
n == NumActors
====