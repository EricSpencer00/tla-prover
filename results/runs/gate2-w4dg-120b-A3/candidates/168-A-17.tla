---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* Alias overridden by the .cfg: n substitutes for the bounded NumActors set.
n == NumActors

Requests == {r \in [actor: n, kind: {"read", "write"}] : TRUE}

VARIABLES rd, wr, queue

vars == <<rd, wr, queue>>

TypeOK ==
    /\ rd \subseteq n
    /\ wr \subseteq n
    /\ queue \in Seq(Requests)

\* No reader and no writer at the start.
Init ==
    /\ rd = {}
    /\ wr = {}
    /\ queue = << >>

\* A process not already waiting joins the queue to read.
RequestRead(p) ==
    /\ \A i \in 1 .. Len(queue): queue[i].actor # p
    /\ queue' = Append(queue, [actor |-> p, kind |-> "read"])
    /\ UNCHANGED <<rd, wr>>

\* A process not already waiting joins the queue to write.
RequestWrite(p) ==
    /\ \A i \in 1 .. Len(queue): queue[i].actor # p
    /\ queue' = Append(queue, [actor |-> p, kind |-> "write"])
    /\ UNCHANGED <<rd, wr>>

\* The head of the queue begins its action: read if nobody is writing; write only
\* if nobody is reading. Either way the request leaves the queue.
Begin ==
    /\ queue # << >>
    /\ wr = {}
    /\ LET head == Head(queue) IN
         /\ head.kind = "read" =>
              /\ rd' = rd \cup {head.actor}
         /\ head.kind = "write" =>
              /\ rd = {}
              /\ wr' = wr \cup {head.actor}
         /\ queue' = Tail(queue)

\* An active reader or writer voluntarily stops.
Stop(p) ==
    /\ p \in rd \/ p \in wr
    /\ rd' = rd \ {p}
    /\ wr' = wr \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in n: RequestRead(p)
    \/ \E p \in n: RequestWrite(p)
    \/ Begin
    \/ \E p \in n: Stop(p)

\* Weak fairness on every action prevents indefinite postponement of any
\* process's request or activity.
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in n: RequestRead(p))
    /\ WF_vars(\E p \in n: RequestWrite(p))
    /\ WF_vars(Begin)
    /\ WF_vars(\E p \in n: Stop(p))

\* Readers and writers are never simultaneously active.
Safety ==
    /\ rd # {} => wr = {}
    /\ wr # {} => rd = {}

\* Every process eventually gets to read and to write. The fairness of the
\* queue -- combined with the actors' own weak fairness -- guarantees none
\* is starved.
Liveness ==
    /\ \A p \in n: (p \in rd) ~> (p \in rd)
    /\ \A p \in n: (p \in wr) ~> (p \in wr)
    /\ \A p \in n: (p \in rd) ~> (p \notin rd)
    /\ \A p \in n: (p \in wr) ~> (p \notin wr)

====