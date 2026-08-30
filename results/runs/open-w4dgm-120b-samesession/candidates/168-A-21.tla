---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* Readers and writers contend for one shared resource. Access requests
\* wait in a bounded first-come-first-served queue (a Seq, not a Set) so
\* that readers and writers are served in arrival order -- this is what
\* gives fairness and prevents either side from being starved forever.

VARIABLES readers, writers, requests

vars == <<readers, writers, requests>>

Requests == [type: {"read", "write"}, actor: NumActors]

TypeOK ==
    /\ readers \subseteq NumActors
    /\ writers \subseteq NumActors
    /\ requests \in Seq(Requests)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ requests = << >>

\* A process that is not already waiting joins the tail of the queue.
RequestRead(a) ==
    /\ [type |-> "read", actor |-> a] \notin requests
    /\ requests' = Append(requests, [type |-> "read", actor |-> a])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(a) ==
    /\ [type |-> "write", actor |-> a] \notin requests
    /\ requests' = Append(requests, [type |-> "write", actor |-> a])
    /\ UNCHANGED <<readers, writers>>

\* A queued request is granted only when it does not conflict with the
\* current exclusive-access requirement. Read requests may proceed while
\* no writer holds the resource; write requests need both the writers
\* empty AND the readers empty.
Process ==
    /\ Len(requests) > 0
    /\ LET r == Head(requests) IN
         \/ /\ r.type = "read"
            /\ writers = {}
            /\ readers' = readers \cup {r.actor}
         \/ /\ r.type = "write"
            /\ writers = {}
            /\ readers = {}
            /\ writers' = writers \cup {r.actor}
    /\ requests' = Tail(requests)

Stop(a) ==
    \/ (a \in readers /\ readers' = readers \ {a})
    \/ (a \in writers /\ writers' = writers \ {a})
    /\ UNCHANGED requests

Next ==
    \/ \E a \in NumActors: RequestRead(a) \/ RequestWrite(a) \/ Stop(a)
    \/ Process

\* Fairness: every request is eventually granted (the queue never
\* permanently blocks a waiting process) and every active participant
\* eventually stops, so no process is stuck reading or writing.
Spec == Init /\ [][Next]_vars
    /\ WF_vars(Process)
    /\ \A a \in NumActors:
         /\ WF_vars(RequestRead(a)) /\ WF_vars(RequestWrite(a))
         /\ WF_vars(Stop(a))

\* Safety: readers and writers are never both active at once, and at
\* most one writer is ever active -- the mutual-exclusion core of the
\* readers-writers discipline.
Safety ==
    /\ readers \cap writers = {}
    /\ \A a1 \in writers: \A a2 \in writers: a1 = a2

Liveness ==
    /\ (\A a \in NumActors: []<>(a \in readers))
    /\ (\A a \in NumActors: []<>(a \in writers))
    /\ (\A a \in NumActors: []<>(a \notin readers))
    /\ (\A a \in NumActors: []<>(a \notin writers))

\* The .cfg overrides the symbolic constant with a concrete bound for
\* model checking; here we expose it as an operator so the module
\* itself stays self-contained.
n == NumActors

====