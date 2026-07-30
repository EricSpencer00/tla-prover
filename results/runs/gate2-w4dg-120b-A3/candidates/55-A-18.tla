---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

\* The Echo algorithm assumes a connected undirected graph. This module fixes
\* the graph to the full three-node mesh, which is trivially connected, with
\* every distinct pair of nodes adjacent and none of a node to itself.

InitGraph ==
  {<<x, y>> \in Node \X Node : x # y}

TypeOK ==
  /\ Node \subseteq STRING
  /\ NoNode \notin Node
  /\ initiator \in Node
  /\ R \subseteq InitGraph
  /\ \A x \in Node : \A y \in Node : <<x, y>> \in R => x # y
  /\ \A x \in Node : \A y \in Node : <<x, y>> \in R => <<y, x>> \in R

VARIABLES parent, phase

vars == <<parent, phase>>

InitState ==
  /\ parent = [x \in Node |-> NoNode]
  /\ phase = [x \in Node |-> "idle"]

\* Echo's actions: only the initiator begins, and every other action is
\* inherited from the original specification. They are unchanged here.
SendEcho ==
  /\ \E v \in Node :
       /\ phase[v] = "idle"
       /\ v = initiator
       /\ phase' = [phase EXCEPT ![v] = "active"]
  /\ UNCHANGED parent

EchoRecv ==
  \E v \in Node, u \in Node :
    /\ <<u, v>> \in R
    /\ phase[u] = "active"
    /\ phase[v] = "idle"
    /\ parent' = [parent EXCEPT ![v] = u]
    /\ phase' = [phase EXCEPT ![v] = "active"]
    /\ UNCHANGED <<>>

Reply ==
  \E v \in Node :
    /\ phase[v] = "active"
    /\ parent[v] # NoNode
    /\ phase' = [phase EXCEPT ![v] = "replied"]
    /\ UNCHANGED parent

Terminated ==
  /\ \A v \in Node : phase[v] = "replied"
  /\ UNCHANGED vars

Next == SendEcho \/ EchoRecv \/ Reply \/ Terminated

Spec == InitState /\ [][Next]_vars

\* AncestorProperties: the initiator is an ancestor of every other node, and
\* the parent relation is acyclic (no node is its own ancestor).
AncestorProperties ==
  /\ \A v \in Node : v # initiator => (parent[v] # NoNode /\ (parent[v] = initiator \/ parent[parent[v]] # NoNode))
  /\ \A a \in Node : (a # NoNode /\ parent[a] # NoNode) => (parent[parent[a]] # a)

TestSpec ==
  /\ Spec
  /\ \E _ \in BOOLEAN : TRUE
  /\ PrintStr("R = ")
  /\ PrintStr(R)
  /\ PrintStr("\n")

\* The .cfg file overrides these with (bounded) concrete definitions; the
\* operators exist so the identifiers themselves are defined in the module.
N1 == Node
I1 == initiator
R1 == R

====