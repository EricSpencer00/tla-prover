---- MODULE MCEcho ----
EXTENDS Naturals, TLC

\* ----------------------------------------------------------------------
\* Constants (to be instantiated by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS Node, initiator, R, NoNode

\* ----------------------------------------------------------------------
\* Derived set of nodes for convenience
\* ----------------------------------------------------------------------
NodeSet == Node

\* ----------------------------------------------------------------------
\* State variables (identical to those of the Echo specification)
\*   - parent[v]  : the current parent of node v (or NoNode if none)
\*   - state[v]  : the phase of node v (0 = idle, 1 = waiting, 2 = done)
\*   - received[v] : the set of messages v has already processed
\* ----------------------------------------------------------------------
VARIABLES parent, state, received

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of all possible messages is the set of ordered pairs (src, dst)
\* where src and dst are distinct nodes.
Msg == { <<src, dst>> : src \in NodeSet, dst \in NodeSet, src # dst }

\* ----------------------------------------------------------------------
\* Initial predicate (instantiates the generic Echo INIT)
\* ----------------------------------------------------------------------
Init ==
    /\ parent = [v \in NodeSet |-> NoNode]
    /\ state  = [v \in NodeSet |-> IF v = initiator THEN 1 ELSE 0]
    /\ received = [v \in NodeSet |-> {}]

\* ----------------------------------------------------------------------
\* Actions (identical to those of the Echo specification)
\* ----------------------------------------------------------------------
Send(v) ==
    /\ v \in NodeSet
    /\ state[v] = 1                 \* waiting to send to all neighbours
    /\ \A u \in NodeSet :
          (<<v, u>> \in R) => 
            /\ state[u] # 2
            /\ parent' = [parent EXCEPT ![u] = v]
            /\ state'  = [state  EXCEPT ![u] = IF parent[u] # NoNode THEN 2 ELSE 1]
            /\ received' = [received EXCEPT ![u] = received[u] \cup {<<v, u>>}]
    /\ UNCHANGED <<parent, state, received>>

Receive(v) ==
    /\ v \in NodeSet
    /\ state[v] = 0                 \* idle, ready to receive
    /\ \E u \in NodeSet :
          (<<u, v>> \in R) /\ <<u, v>> \notin received[v] /\ parent[v] = NoNode
          /\ parent' = [parent EXCEPT ![v] = u]
          /\ state'  = [state  EXCEPT ![v] = 1]
          /\ received' = [received EXCEPT ![v] = received[v] \cup {<<u, v>>}]
    /\ UNCHANGED <<parent, state, received>>

Done(v) ==
    /\ v \in NodeSet
    /\ state[v] = 1
    /\ \A u \in NodeSet : (<<v, u>> \in R) => <<v, u>> \in received[v]
    /\ state' = [state EXCEPT ![v] = 2]
    /\ UNCHANGED <<parent, received>>

Next ==
    \/ \E v \in NodeSet : Send(v)
    \/ \E v \in NodeSet : Receive(v)
    \/ \E v \in NodeSet : Done(v)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
TestSpec == Init /\ [][Next]_<<parent, state, received>>

\* ----------------------------------------------------------------------
\* Safety invariant: type correctness
\* ----------------------------------------------------------------------
TypeOK ==
    /\ parent \in [NodeSet -> NoNode \cup NodeSet]
    /\ state  \in [NodeSet -> {0, 1, 2}]
    /\ received \in [NodeSet -> SUBSET Msg]

\* ----------------------------------------------------------------------
\* Safety invariant: ancestor properties (acyclic and initiator is ancestor)
\* ----------------------------------------------------------------------
AncestorProperties ==
    /\ \A v \in NodeSet :
          parent[v] = NoNode => v = initiator
    /\ \A v \in NodeSet :
          (parent[v] # NoNode) => v # initiator /\ parent[parent[v]] # v

\* ----------------------------------------------------------------------
\* Theorems (optional, just to expose the invariants to the .cfg)
\* ----------------------------------------------------------------------
THEOREM SpecImpliesTypeOK == TestSpec => []TypeOK
THEOREM SpecImpliesAncestor == TestSpec => []AncestorProperties

====