---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, FiniteSets

(*--------------------------------------------------------------------
  Constants required by the reference .cfg
--------------------------------------------------------------------*)
CONSTANT Node          \* the set of all nodes
CONSTANT initiator     \* the distinguished initiator node
CONSTANT R             \* the adjacency relation (undirected graph)
CONSTANT NoNode        \* a sentinel value distinct from all nodes

(*--------------------------------------------------------------------
  Derived sets
--------------------------------------------------------------------*)
Nodes == Node

(*--------------------------------------------------------------------
  State variables (exactly those used by the Echo specification)
--------------------------------------------------------------------*)
VARIABLES parent, sent, received, done

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
NoParent == NoNode

IsEdge(x, y) == <<x, y>> \in R

Neighbors(n) == { m \in Nodes : IsEdge(n, m) }

(*--------------------------------------------------------------------
  Type correctness predicate (used as an invariant)
--------------------------------------------------------------------*)
TypeOK == 
    /\ parent \in [Nodes -> Nodes \cup {NoParent}]
    /\ sent \in [Nodes -> SUBSET Nodes]
    /\ received \in [Nodes -> SUBSET Nodes]
    /\ done \in [Nodes -> BOOLEAN]

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ parent = [n \in Nodes |-> NoParent]
    /\ sent = [n \in Nodes |-> {}]
    /\ received = [n \in Nodes |-> {}]
    /\ done = [n \in Nodes |-> FALSE]
    /\ parent[initiator] = initiator   \* the initiator is its own ancestor

(*--------------------------------------------------------------------
  Action definitions (as in the Echo specification)
--------------------------------------------------------------------*)
Send(u, v) ==
    /\ u # v
    /\ IsEdge(u, v)
    /\ ~ (v \in sent[u])
    /\ parent[v] = NoParent
    /\ sent' = [sent EXCEPT ![u] = sent[u] \cup {v}]
    /\ UNCHANGED <<parent, received, done>>

Receive(v, u) ==
    /\ v # u
    /\ IsEdge(v, u)
    /\ u \in sent[v]
    /\ v \notin received[u]
    /\ received' = [received EXCEPT ![u] = received[u] \cup {v}]
    /\ parent' = [parent EXCEPT ![u] = v]
    /\ UNCHANGED <<sent, done>>

DoneAction(v) ==
    /\ parent[v] # NoParent
    /\ \A w \in Nodes : (v # w) => (v \in received[w])
    /\ done' = [done EXCEPT ![v] = TRUE]
    /\ UNCHANGED <<parent, sent, received>>

EchoStep ==
    \/ \E u, v \in Nodes : Send(u, v)
    \/ \E u, v \in Nodes : Receive(u, v)
    \/ \E v \in Nodes : DoneAction(v)

Next == EchoStep

(*--------------------------------------------------------------------
  Safety property: ancestor relation is a tree rooted at initiator
--------------------------------------------------------------------*)
Ancestor(v) ==
    IF v = initiator THEN {initiator}
    ELSE IF parent[v] = NoParent THEN {}
    ELSE {v} \cup Ancestor(parent[v])

AncestorProperties ==
    /\ \A v \in Nodes : ancestor = Ancestor(v)
       /\ (v = initiator) => (ancestor = {initiator})
    /\ \A v \in Nodes : initiator \in Ancestor(v) \/ v = initiator
    /\ \A v \in Nodes : v \notin Ancestor(parent[v])   \* acyclicity

(*--------------------------------------------------------------------
  Specification formula required by the .cfg
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<parent, sent, received, done>>

TestSpec == Spec

=============================================================================