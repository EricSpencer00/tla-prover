---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node initiator, R, NoNode

VARIABLES token, holder, pending, done, searchEdge, parent

vars == <<token, holder, pending, done, searchEdge, parent>>

Edges == {e \in [Node -> Node] : e[1] # e[2]}
Endpoints == {e[1] : e \in Edges} \union {e[2] : e \in Edges}
ActivePairs == [p \in Node \X Node |> p[1] # p[2]]

TypeOK ==
    /\ token \in {"free", "inuse"}
    /\ holder \in Node \union {NoNode}
    /\ pending \in SUBSET ActivePairs
    /\ done \in SUBSET Node
    /\ searchEdge \in [Node -> Node \union {NoNode}]
    /\ parent \in [Node -> Node \union {NoNode}]

Init ==
    /\ token = "free"
    /\ holder = NoNode
    /\ pending = {}
    /\ done = {}
    /\ searchEdge = [n \in Node |-> NoNode]
    /\ parent = [n \in Node |-> NoNode]

Enter(n) ==
    /\ token = "free"
    /\ n \notin done
    /\ token' = "inuse"
    /\ holder' = n
    /\ UNCHANGED <<pending, done, searchEdge, parent>>

Search(m, n) ==
    /\ holder = m
    /\ <<m, n>> \in Edges
    /\ m # n
    /\ n \notin done
    /\ m # initiator
    /\ m \notin done
    /\ n \notin done
    /\ n \notin pending
    /\ pending' = pending \union {<<m, n>>}
    /\ UNCHANGED <<token, holder, done, searchEdge, parent>>

Grant(m, n) ==
    /\ <<m, n>> \in pending
    /\ parent[n] = NoNode
    /\ parent' = [parent EXCEPT ![n] = m]
    /\ searchEdge' = [searchEdge EXCEPT ![n] = <<m, n>>]
    /\ pending' = pending \ {<<m, n>>}
    /\ UNCHANGED <<token, holder, done>>

Abort(m, n) ==
    /\ <<m, n>> \in pending
    /\ parent[n] # NoNode
    /\ pending' = pending \ {<<m, n>>}
    /\ UNCHANGED <<token, holder, done, searchEdge, parent>>

Complete(n) ==
    /\ holder = n
    /\ token' = "free"
    /\ holder' = NoNode
    /\ done' = done \union {n}
    /\ UNCHANGED <<pending, searchEdge, parent>>

Reset ==
    /\ \A n \in Node : n \in done
    /\ token' = "free"
    /\ holder' = NoNode
    /\ pending' = {}
    /\ done' = {}
    /\ searchEdge' = [n \in Node |-> NoNode]
    /\ parent' = [n \in Node |-> NoNode]

EnterStep == \E n \in Node : Enter(n)
SearchStep == \E m, n \in Endpoints : Search(m, n)
GrantStep == \E m, n \in Endpoints : Grant(m, n)
AbortStep == \E m, n \in Endpoints : Abort(m, n)
CompleteStep == \E n \in Node : Complete(n)

Next == EnterStep \/ SearchStep \/ GrantStep \/ AbortStep \/ CompleteStep \/ Reset

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(EnterStep)
    /\ SF_vars(SearchStep)
    /\ WF_vars(GrantStep \/ AbortStep)
    /\ WF_vars(CompleteStep)

AncestorProperties ==
    /\ \A n \in Node : n # initiator => parent[n] # NoNode
    /\ \A n \in Node : (n # initiator /\ parent[n] # NoNode) => parent[parent[n]] # NoNode

TestSpec == Spec

N1 == Node
I1 == initiator
R1 == R

====