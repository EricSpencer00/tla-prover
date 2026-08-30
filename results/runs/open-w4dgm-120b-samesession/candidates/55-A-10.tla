---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

\* A fully-meshed three-node graph; every pair of distinct nodes is connected.
\* This concrete choice keeps the state space tiny so TLC can explore it exhaustively.
Nodes == {"n1", "n2", "n3"}
Succ(n) == CASE n = "n1" -> "n2"
             [] n = "n2" -> "n3"
             [] n = "n3" -> "n1"
Edges == {p \in Nodes \X Nodes : p[1] # p[2]}
Ring == UNION {[n, Succ(n)] : n \in Nodes}

TypeOK ==
    /\ Nodes \subseteq Node
    /\ R \subseteq Nodes
    /\ initiator \in Nodes
    /\ NoNode \notin Node

\* The Echo algorithm's shared pool is the joined ring plus the initiator's own edge.
\* The initiator may be on the ring already; the union is what keeps the pool closed.
Pool == Ring \cup {<<initiator, Succ(initiator)>>}

VARIABLES awake, request, parent, sent, printed
vars == <<awake, request, parent, sent, printed>>

Init ==
    /\ awake = {initiator}
    /\ request = {}
    /\ parent = [n \in Nodes |-> NoNode]
    /\ sent = {}
    /\ printed = FALSE

\* An already-awake node forwards the echo request to any neighbor it has not yet heard from.
SendEcho(e) ==
    /\ e \in Pool
    /\ e[1] \in awake
    /\ e[2] \notin awake
    /\ request' = request \cup {e}
    /\ UNCHANGED <<awake, parent, sent, printed>>

\* Any pending request is delivered to its target, who records its sender as parent.
DeliverEcho(e) ==
    /\ e \in request
    /\ request' = request \ {e}
    /\ awake' = awake \cup {e[2]}
    /\ parent' = [parent EXCEPT ![e[2]] = e[1]]
    /\ UNCHANGED <<sent, printed>>

\* A node that heard the echo may emit its own response toward its parent; each response
\* is sent at most once, since sending is guarded on not having sent it before.
SendResponse(e) ==
    /\ e[1] \in awake
    /\ e[1] \notin R
    /\ e[2] = parent[e[1]]
    /\ <<e[1], e[2]>> \notin sent
    /\ sent' = sent \cup {<<e[1], e[2]>>}
    /\ UNCHANGED <<awake, request, parent, printed>>

\* A delivered response is delivered up the tree toward the initiator.
DeliverResponse(e) ==
    /\ e \in sent
    /\ sent' = sent \ {e}
    /\ IF e[2] = initiator
       THEN R' = R \cup {e[1]}
       ELSE request' = request \cup {<<e[2], parent[e[2]]>>}
    /\ UNCHANGED <<awake, parent, printed>>

\* At the very end, with every node awake and every response delivered, the model
\* emits a one-time trace print and takes no further steps.
PrintTrace ==
    /\ \A n \in Nodes : n \in awake
    /\ \A e \in sent : e[2] = initiator
    /\ ~printed
    /\ printed' = TRUE
    /\ UNCHANGED <<awake, request, parent, sent>>

Next ==
    \/ \E e \in Pool : SendEcho(e)
    \/ \E e \in Pool : DeliverEcho(e)
    \/ \E e \in Pool : SendResponse(e)
    \/ \E e \in Pool : DeliverResponse(e)
    \/ PrintTrace

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E e \in Pool : SendEcho(e))
    /\ WF_vars(\E e \in Pool : DeliverEcho(e))
    /\ WF_vars(\E e \in Pool : SendResponse(e))
    /\ WF_vars(\E e \in Pool : DeliverResponse(e))
    /\ WF_vars(PrintTrace)

AncestorProperties ==
    /\ \A n \in Nodes : (n # initiator) => (parent[n] # NoNode)
    /\ \A n \in Nodes : (n # initiator) => (n \in R)
    /\ \A n \in Nodes : (n \in R) => (n \in awake)
    /\ \A n \in Nodes : (n # initiator /\ n \in awake) ~> (initiator \in awake)

TestSpec == Spec
====