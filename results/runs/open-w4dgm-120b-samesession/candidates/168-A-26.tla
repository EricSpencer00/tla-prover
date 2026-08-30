---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* Types: readers, writers, and the request queue (each entry is a kind/process pair).
Readers == 0..(NumActors - 1)
Writers == 0..(NumActors - 1)
Kinds == {"read", "write"}
Requests == [kind: Kinds, actor: Readers \cup Writers]

VARIABLES activeReaders, activeWriter, queue

vars == << activeReaders, activeWriter, queue >>

TypeOK ==
    /\ activeReaders \subseteq Readers
    /\ activeWriter \subseteq Writers
    /\ queue \in Seq(Requests)

Init ==
    /\ activeReaders = {}
    /\ activeWriter = {}
    /\ queue = << >>

\* Actors request read/write access by joining the end of the waiting queue.
RequestRead(a) ==
    /\ [kind |-> "read", actor |-> a] \notin {queue[i] : i \in 1..Len(queue)}
    /\ queue' = Append(queue, [kind |-> "read", actor |-> a])
    /\ UNCHANGED << activeReaders, activeWriter >>

RequestWrite(a) ==
    /\ [kind |-> "write", actor |-> a] \notin {queue[i] : i \in 1..Len(queue)}
    /\ queue' = Append(queue, [kind |-> "write", actor |-> a])
    /\ UNCHANGED << activeReaders, activeWriter >>

\* The queue grants access in order; writing requires exclusive access, reading needs no writer.
Grant ==
    /\ Len(queue) > 0
    /\ activeWriter = {}
    /\ LET h == Head(queue) IN
        \/ /\ h.kind = "read"
           /\ activeReaders' = activeReaders \cup {h.actor}
           /\ activeWriter' = activeWriter
        \/ /\ h.kind = "write"
           /\ activeReaders = {}
           /\ activeWriter' = activeWriter \cup {h.actor}
           /\ activeReaders' = activeReaders
    /\ queue' = Tail(queue)

StopActivity(a) ==
    /\ (a \in activeReaders \/ a \in activeWriter)
    /\ activeReaders' = activeReaders \ {a}
    /\ activeWriter' = activeWriter \ {a}
    /\ UNCHANGED queue

Next ==
    \/ \E a \in Readers : RequestRead(a)
    \/ \E a \in Writers : RequestWrite(a)
    \/ Grant
    \/ \E a \in Readers \cup Writers : StopActivity(a)

Spec == Init /\ [][Next]_vars
    /\ WF_vars(Grant)
    /\ \A a \in Readers \cup Writers :
        /\ SF_vars(RequestRead(a)) /\ SF_vars(RequestWrite(a))
        /\ SF_vars(StopActivity(a))

\* Safety: readers and writers are never active together, and at most one writer.
Safety ==
    /\ (activeWriter # {} => activeReaders = {})
    /\ (activeReaders # {} => activeWriter = {})
    /\ Cardinality(activeWriter) <= 1

\* Liveness: every process eventually reads and eventually writes.
Liveness ==
    \A a \in Readers \cup Writers :
        /\ (a \in Readers) ~> (a \in activeReaders)
        /\ (a \in Writers) ~> (a \in activeWriter)

\* The .cfg file maps the concrete pool size to the symbolic constant NumActors.
n == NumActors

====