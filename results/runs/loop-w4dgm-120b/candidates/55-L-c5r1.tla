---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, initiator, R, NoNode

VARIABLES set, parent, version, pending, echoing, answered

vars == <<set, parent, version, pending, echoing, answered>>

Bump(v) == IF v < 2 THEN v + 1 ELSE 0

TypeOK ==
    /\ set \subseteq Node
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ version \in 0..2
    /\ pending \subseteq (Node \X Node \X (0..2))
    /\ echoing \subseteq Node
    /\ answered \subseteq Node

Ancestor(n) == {n} \cup IF parent[n] = NoNode THEN {} ELSE Ancestor(parent[n])

AncestorProperties ==
    /\ \A n \in Node : initiator \in Ancestor(n)
    /\ \A m, n \in Node : (parent[n] = m) => (parent[m] # n)

Init ==
    /\ set = {}
    /\ parent = [n \in Node |-> NoNode]
    /\ version = 0
    /\ pending = {}
    /\ echoing = {}
    /\ answered = {}

Echo(n) ==
    /\ n \notin echoing
    /\ echoing' = echoing \cup {n}
    /\ UNCHANGED <<set, parent, version, pending, answered>>

Reply(m, n) ==
    /\ n \in echoing
    /\ m \in set
    /\ parent[n] = NoNode
    /\ n # initiator
    /\ <<n, m, version>> \notin pending
    /\ pending' = pending \cup {<<n, m, version>>}
    /\ UNCHANGED <<set, parent, version, echoing, answered>>

Apply(m, n, v) ==
    /\ <<n, m, v>> \in pending
    /\ v = version
    /\ parent[n] = NoNode
    /\ parent' = [parent EXCEPT ![n] = m]
    /\ version' = Bump(v)
    /\ pending' = pending \ {<<n, m, v>>}
    /\ UNCHANGED <<set, echoing, answered>>

Dispose(m, n, v) ==
    /\ <<n, m, v>> \in pending
    /\ (v # version \/ parent[n] # NoNode)
    /\ pending' = pending \ {<<n, m, v>>}
    /\ UNCHANGED <<set, parent, version, echoing, answered>>

Admit(n) ==
    /\ n \notin set
    /\ n \notin answered
    /\ set' = set \cup {n}
    /\ answered' = answered \cup {n}
    /\ UNCHANGED <<parent, version, pending, echoing>>

EchoStep == \E n \in Node : Echo(n)

ReplyStep == \E m \in Node, n \in Node : Reply(m, n)

ApplyStep == \E m \in Node, n \in Node, v \in 0..2 : Apply(m, n, v)

DisposeStep == \E m \in Node, n \in Node, v \in 0..2 : Dispose(m, n, v)

AdmitStep == \E n \in Node : Admit(n)

Next == EchoStep \/ ReplyStep \/ ApplyStep \/ DisposeStep \/ AdmitStep

InitSpec == Init /\ [][Next]_vars

TraceAdmit ==
    /\ AdmitStep
    /\ EchoStep
    /\ UNCHANGED <<set, parent, version, pending, echoing, answered>>

TraceReply ==
    /\ ReplyStep
    /\ EchoStep
    /\ UNCHANGED <<set, parent, version, pending, echoing, answered>>

TraceApply ==
    /\ ApplyStep
    /\ EchoStep
    /\ UNCHANGED <<set, parent, version, pending, echoing, answered>>

TraceDispose ==
    /\ DisposeStep
    /\ EchoStep
    /\ UNCHANGED <<set, parent, version, pending, echoing, answered>>

TraceSteps ==
    TraceAdmit \/ TraceReply \/ TraceApply \/ TraceDispose

TestSpec == InitSpec /\ WF_vars(TraceApply) /\ WF_vars(TraceDispose) /\ SF_vars(TraceSteps)

Spec == InitSpec /\ [][Next]_vars /\ WF_vars(TraceSteps)

====