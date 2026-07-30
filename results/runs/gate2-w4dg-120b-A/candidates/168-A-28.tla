---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Actor == 0 .. (NumActors - 1)
ReqType == {"read", "write"}
Req == [ty : ReqType, a : Actor]
Reqs == [ty : ReqType, a : Actor]

VARIABLES ldrs, wdrs, queue

vars == <<ldrs, wdrs, queue>>

TypeOK ==
    /\ ldrs \subseteq Actor
    /\ wdrs \subseteq Actor
    /\ queue \in Seq(Reqs)

Init ==
    /\ ldrs = {}
    /\ wdrs = {}
    /\ queue = << >>

\* A process that is not already queued asks for read access.
RequestRead(a) ==
    /\ \A i \in 1 .. Len(queue) : queue[i].a # a
    /\ queue' = Append(queue, [ty |-> "read", a |-> a])
    /\ UNCHANGED <<ldrs, wdrs>>

\* A process that is not already queued asks for write access.
RequestWrite(a) ==
    /\ \A i \in 1 .. Len(queue) : queue[i].a # a
    /\ queue' = Append(queue, [ty |-> "write", a |-> a])
    /\ UNCHANGED <<ldrs, wdrs>>

\* The queue is served in order; a writer needs the resource completely free.
Serve ==
    /\ queue # << >>
    /\ wdrs = {}
    /\ LET h == Head(queue) IN
         /\ IF h.ty = "read" THEN ldrs' = ldrs \cup {h.a}
            ELSE IF ldrs = {} THEN wdrs' = wdrs \cup {h.a}
            ELSE ldrs' = ldrs
         /\ queue' = Tail(queue)
    /\ UNCHANGED <<wdrs>>

StopRead(a) ==
    /\ a \in ldrs
    /\ ldrs' = ldrs \ {a}
    /\ UNCHANGED <<wdrs, queue>>

StopWrite(a) ==
    /\ a \in wdrs
    /\ wdrs' = wdrs \ {a}
    /\ UNCHANGED <<ldrs, queue>>

Next ==
    \/ \E a \in Actor : RequestRead(a)
    \/ \E a \in Actor : RequestWrite(a)
    \/ Serve
    \/ \E a \in Actor : StopRead(a)
    \/ \E a \in Actor : StopWrite(a)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E a \in Actor : RequestRead(a))
    /\ WF_vars(\E a \in Actor : RequestWrite(a))
    /\ WF_vars(Serve)
    /\ WF_vars(\E a \in Actor : StopRead(a))
    /\ WF_vars(\E a \in Actor : StopWrite(a))

\* Readers and writers never occupy the resource at the same time.
Safety ==
    /\ (wdrs # {} => ldrs = {})
    /\ (ldrs # {} => wdrs = {})
    /\ \A a, b \in wdrs : a = b

\* Every process eventually gets to read, and every active reader stops.
\* Together these keep the queue from starving any request.
Liveness ==
    /\ \A a \in Actor : (a \in ldrs) ~> (a \notin ldrs)
    /\ \A a \in Actor : (a \in wdrs) ~> (a \notin wdrs)

====