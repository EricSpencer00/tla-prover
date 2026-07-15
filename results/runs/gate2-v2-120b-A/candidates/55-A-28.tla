---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, TLC

(*--------------------------------------------------------------------
  Constants (to be bound in the .cfg file)
--------------------------------------------------------------------*)
CONSTANTS
    Node,      \* The set of node identifiers (three distinct strings)
    initiator, \* The distinguished initiator node, element of Node
    R,         \* Undirected adjacency relation: a set of unordered pairs {i,j}
    NoNode     \* Sentinel value distinct from all nodes, used as "no parent"

(*--------------------------------------------------------------------
  Derived constant: the set of ordered parent links (for convenience)
--------------------------------------------------------------------*)
Parents == { [child |-> n, parent |-> p] : n \in Node, p \in Node }

(*--------------------------------------------------------------------
  State variable: parent mapping (each node either has a parent or NoNode)
--------------------------------------------------------------------*)
VARIABLES parent

(*--------------------------------------------------------------------
  Type correctness (used as an invariant)
--------------------------------------------------------------------*)
TypeOK == 
    /\ parent \in [Node -> (Node \cup {NoNode})]
    /\ NoNode \notin Node
    /\ initiator \in Node
    /\ initiator \in Node

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
\* The set of nodes that have already received the echo message
Received == { n \in Node : parent[n] # NoNode }

\* The initiator starts with parent = NoNode
IsInitiator(n) == n = initiator

(*--------------------------------------------------------------------
  Initial state (same as Echo specification)
--------------------------------------------------------------------*)
Init == 
    /\ parent = [n \in Node |-> 
        IF IsInitiator(n) THEN NoNode ELSE NoNode] \* all nodes start with NoNode
    /\ parent[initiator] = NoNode   \* explicit for readability

(*--------------------------------------------------------------------
  Actions (inherit Echo behavior)
--------------------------------------------------------------------*)
\* A node that has not yet received the echo can receive it from any neighbor
Receive(n) == 
    /\ n \in Node
    /\ parent[n] = NoNode
    /\ \E m \in Node :
          /\ parent[m] # NoNode          \* m has already received the echo
          /\ {n,m} \in R                 \* (n,m) is an edge in the undirected graph
    /\ parent' = [parent EXCEPT ![n] = m]

\* The initiator can terminate when all nodes have been reached
Terminate == 
    /\ parent[initiator] = NoNode
    /\ \A n \in Node : parent[n] # NoNode
    /\ UNCHANGED parent

Next == 
    \/ \E n \in Node : Receive(n)
    \/ Terminate

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<parent>>

(*--------------------------------------------------------------------
  TestSpec: same as Spec but prints the adjacency relation at start
--------------------------------------------------------------------*)
TestSpec == 
    /\ Init
    /\ PrintAdjacency
    /\ [][Next]_<<parent>>

PrintAdjacency == 
    Print("\* Graph adjacency relation R = " ^ ToString(R))

(*--------------------------------------------------------------------
  Ancestor relation derived from parent mapping
--------------------------------------------------------------------*)
Ancestor == 
    { <<x, y>> \in Node \X Node :
        \E p \in Seq(Node) :
            /\ Len(p) >= 1
            /\ p[1] = y
            /\ p[Len(p)] = x
            /\ \A i \in 1..(Len(p)-1) : parent[p[i]] = p[i+1] }

(*--------------------------------------------------------------------
  Safety property: initiator is ancestor of all other nodes,
  and the ancestor relation is acyclic.
--------------------------------------------------------------------*)
AncestorProperties == 
    /\ \A n \in Node \ {initiator} : <<n, initiator>> \in Ancestor
    /\ \A n \in Node : <<n, n>> \notin Ancestor

=============================================================================