---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

VARIABLES
  parent,      \* parent[n]: the node echo messages coming from n are routed through
  awaiting,    \* awaiting[n]: whether node n has not yet contributed to the echo
  acked,       \* acked[n]: whether the echo from n has been acknowledged at the initiator
  phase        \* phase of the algorithm: "idle", "growing", or "done"

vars == <<parent, awaiting, acked, phase>>

Nodes == Node
Edges == {p \in Nodes \X Nodes : p[1] # p[2]}
Alpha == CHOOSE n \in Nodes : TRUE
AncestorOf(n) == {m \in Nodes : m # n /\ parent[m] # NoNode /\ parent[m] = n}
Below(n) == IF n = Alpha THEN "initiator"
            ELSE IF parent[n] = NoNode THEN "disconnected"
            ELSE "below " \o parent[n]

TypeOK ==
  /\ parent \in [Nodes -> Nodes \union {NoNode}]
  /\ awaiting \in [Nodes -> BOOLEAN]
  /\ acked \in [Nodes -> BOOLEAN]
  /\ phase \in {"idle", "growing", "done"}

\* Acknowledgement only ever arrives from below a node that joined the tree; the
\* initiator is therefore an ancestor of every participating node.
AncestorProperties ==
  /\ \A n \in Nodes : n # initiator /\ acked[n] => (parent[n] \in AncestorOf(n) \union {initiator})
  /\ \A a, b \in Nodes :
       (b \in AncestorOf(a) /\ a \in AncestorOf(b)) => (a = b \/ parent[a] = NoNode)

Init ==
  /\ parent = [n \in Nodes |-> NoNode]
  /\ awaiting = [n \in Nodes |-> TRUE]
  /\ acked = [n \in Nodes |-> FALSE]
  /\ phase = "idle"

StartGrowth ==
  /\ phase = "idle"
  /\ phase' = "growing"
  /\ UNCHANGED <<parent, awaiting, acked>>

\* The initiator claims itself as its own parent; this is what makes it its own
\* ancestor and keeps it out of every other node's ancestor set.
Claim(n, a) ==
  /\ phase = "growing"
  /\ awaiting[n]
  /\ <<n, a>> \in Edges
  /\ parent[n] = NoNode
  /\ parent' = [parent EXCEPT ![n] = IF n = initiator THEN initiator ELSE a]
  /\ UNCHANGED <<awaiting, acked, phase>>

\* A leaf acknowledged its echo only after its parent acknowledged.
Acknowledge(n) ==
  /\ phase = "growing"
  /\ awaiting[n]
  /\ parent[n] # NoNode
  /\ (n = initiator \/ acked[parent[n]])
  /\ awaiting' = [awaiting EXCEPT ![n] = FALSE]
  /\ acked' = [acked EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<parent, phase>>

FinishGrowth ==
  /\ phase = "growing"
  /\ \A n \in Nodes : ~awaiting[n]
  /\ phase' = "done"
  /\ UNCHANGED <<parent, awaiting, acked>>

Next ==
  \/ StartGrowth
  \/ \E n \in Nodes, a \in Nodes : Claim(n, a)
  \/ \E n \in Nodes : Acknowledge(n)
  \/ FinishGrowth

Spec == Init /\ [][Next]_vars

TestSpec ==
  /\ Spec
  /\ \A a, b \in Nodes : a # b => <<a, b>> \in Edges
  /\ UNCHANGED <<Node, initiator, R, NoNode>>

====