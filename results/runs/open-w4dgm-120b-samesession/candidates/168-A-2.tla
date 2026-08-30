---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

\* Readers-writers coordination via a bounded FIFO request queue.  The
\* two mutually-exclusive safety properties (no writer while readers are
\* active, and at most one writer at a time) together with the fairness
\* assumptions below guarantee that no process is starved of either
\* resource: every process that begins reading or writing eventually
\* stops, and weak fairness on the queue means every queued process is
\* eventually serviced in FIFO order.

CONSTANTS NumActors

Requests == {"read", "write"}
Actors == 1..NumActors

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

NoActor == 0

\* The waiting queue carries both the process and its mode (read or write)
\* as an ordered sequence so the next grant is always the request at the
\* head of the line, giving first-come-first-served fairness.
Waiting == {<<m, a>> : m \in Requests, a \in Actors}

TypeOK ==
    /\ reading \subseteq Actors
    /\ writing \subseteq Actors
    /\ queue \in Seq(Waiting)

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = <<>>

RequestRead(a) ==
    /\ << "read", a >> \notin queue
    /\ queue' = Append(queue, << "read", a >>)
    /\ UNCHANGED << reading, writing >>

RequestWrite(a) ==
    /\ << "write", a >> \notin queue
    /\ queue' = Append(queue, << "write", a >>)
    /\ UNCHANGED << reading, writing >>

\* Grant the head of the queue only when it would not violate mutual
\* exclusion: a writer must wait for all readers to finish, and a reader
\* must wait while any writer is active.
Grant ==
    /\ Len(queue) > 0
    /\ writing = {}
    /\ LET m == Head(queue)[1]
           a == Head(queue)[2]
       IN /\ (m = "read" \/ writing = {})
          /\ (m = "write" => reading = {})
          /\ reading' = IF m = "read" THEN reading \cup {a} ELSE reading
          /\ writing' = IF m = "write" THEN writing \cup {a} ELSE writing
    /\ queue' = Tail(queue)

Stop(a) ==
    /\ a \in reading \/ a \in writing
    /\ reading' = reading \ {a}
    /\ writing' = writing \ {a}
    /\ UNCHANGED queue

Next ==
    \/ \E a \in Actors : RequestRead(a)
    \/ \E a \in Actors : RequestWrite(a)
    \/ Grant
    \/ \E a \in Actors : Stop(a)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Grant)
    /\ \A a \in Actors : SF_vars(Stop(a))
    /\ \A a \in Actors : WF_vars(RequestRead(a))
    /\ \A a \in Actors : WF_vars(RequestWrite(a))

\* Mutual exclusion is enforced by two complementary directions, so the
\* two properties below together cover the full read/write conflict.
Safety ==
    /\ (writing # {} => reading = {})
    /\ \A a, b \in Actors : (a \in writing /\ b \in writing) => a = b

Liveness ==
    \A a \in Actors :
        /\ (a \in Actors) ~> (a \in reading \/ a \in writing)
        /\ (a \in reading \/ a \in writing) ~> (a \notin reading /\ a \notin writing)

\* Model-checking convenience: the actor count is fixed at runtime, but
\* the .cfg substitutes it in with a concrete bounded value.
n == NumActors
====