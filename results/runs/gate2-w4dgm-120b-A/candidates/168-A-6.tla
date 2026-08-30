---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

\* Model: a readers-writers solution with a first-come-first-served request queue,
\* checked against the invariant that readers and writers are never active together.
CONSTANTS NumActors

Ids == 1..NumActors
Modes == {"read", "write"}

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

TypeOK ==
    /\ reading \subseteq Ids
    /\ writing \subseteq Ids
    /\ queue \in Seq([pid: Ids, mode: Modes])

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = <<>>

\* A process joins the wait queue to request read access.
RequestRead ==
    /\ \A i \in 1..Len(queue) : queue[i].pid # n \/ queue[i].mode # "read"
    /\ queue' = Append(queue, [pid |-> n, mode |-> "read"])
    /\ UNCHANGED <<reading, writing>>

\* A process joins the wait queue to request write access.
RequestWrite ==
    /\ \A i \in 1..Len(queue) : queue[i].pid # n \/ queue[i].mode # "write"
    /\ queue' = Append(queue, [pid |-> n, mode |-> "write"])
    /\ UNCHANGED <<reading, writing>>

\* Grant the head request only when it would not violate the readers-writers
\* exclusion rule: writers require nobody reading, readers require no writer.
Grant ==
    /\ queue # <<>>
    /\ writing = {}
    /\ LET h == Head(queue) IN
        /\ \/ h.mode = "read"
           \/ (h.mode = "write" /\ reading = {})
        /\ IF h.mode = "read"
           THEN reading' = reading \cup {h.pid}
           ELSE writing' = writing \cup {h.pid}
        /\ queue' = Tail(queue)
    /\ UNCHANGED <<reading, writing>>

\* A process voluntarily stops reading or writing, freeing the resource.
Stop ==
    /\ \/ reading # {}
       \/ writing # {}
    /\ reading' = IF reading # {} THEN reading \ {n} ELSE reading
    /\ writing' = IF writing # {} THEN writing \ {n} ELSE writing
    /\ UNCHANGED queue

Next == RequestRead \/ RequestWrite \/ Grant \/ Stop

Spec == Init /\ [][Next]_vars
    /\ \A a \in {RequestRead, RequestWrite, Grant, Stop} : WF_vars(a)

\* Readers and writers are never active together; at most one writer active.
Safety == (writing # {}) => (reading = {})
    /\ \A w1, w2 \in writing : w1 = w2

Liveness == \A p \in Ids :
    /\ (p \in reading) ~> (p \notin reading)
    /\ (p \in writing) ~> (p \notin writing)
    /\ (\A i \in 1..Len(queue) : queue[i].pid # p) ~> (p \in reading)
    /\ (\A i \in 1..Len(queue) : queue[i].pid # p) ~> (p \in writing)

\* n is a concrete process identifier, mapped in the .cfg to each value in turn.
n == CHOOSE x \in Ids : TRUE
====