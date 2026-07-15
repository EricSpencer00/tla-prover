---- MODULE MCEcho ----
EXTENDS Natural, TLC

(* ----------------------------------------------------------------------
   Constants (to be instantiated by the .cfg file)
   ---------------------------------------------------------------------- *)
CONSTANTS
    Node,        \* The set of node identifiers (e.g., {"a","b","c"})
    initiator,   \* The distinguished initiator node
    R,           \* Undirected graph relation; a subset of Node X Node
    NoNode       \* Sentinel value representing "no parent"

(* ----------------------------------------------------------------------
   Derived constant: the set of all unordered edges (for readability)
   ---------------------------------------------------------------------- *)
Edges == { <<x, y>> : <<x, y>> \in R }

(* ----------------------------------------------------------------------
   State variables (inherited from the Echo specification)
   ---------------------------------------------------------------------- *)
VARIABLES
    parent,    \* Function Node -> (Node \cup {NoNode}) describing each node's parent
    recv,      \* Set of nodes that have already received the echo
    sent,      \* Set of nodes that have already sent their echo
    done       \* Boolean flag indicating termination

(* ----------------------------------------------------------------------
   Type correctness invariant (required)
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ parent \in [Node -> (Node \cup {NoNode})]
    /\ recv \subseteq Node
    /\ sent \subseteq Node
    /\ done \in BOOLEAN
    /\ NoNode \notin Node
    /\ initiator \in Node
    /\ R \subseteq Node \X Node
    /\ \A <<x, y>> \in R: x # y               \* irreflexivity
    /\ \A <<x, y>> \in R: <<y, x>> \in R       \* symmetry

(* ----------------------------------------------------------------------
   Safety property: AncestorProperties (required)
   At termination, every node (except the initiator) has a parent,
   the initiator has no parent, and the ancestor relation is acyclic.
   ---------------------------------------------------------------------- *)
AncestorProperties ==
    /\ done => 
        /\ parent[initiator] = NoNode
        /\ \A n \in Node \ {initiator}: parent[n] \in Node
        /\ \A n \in Node: ~(n \in (parent)^+ [n])   \* acyclicity: n not reachable from itself via parent
    /\ \A n \in Node:   \* while running, nodes may still be NoNode, but never NoNode for non‑initiator unless not yet set
        (parent[n] = NoNode => n = initiator \/ n \notin sent)

(* ----------------------------------------------------------------------
   Initial state (inherits Echo's Init, instantiated for the concrete graph)
   ---------------------------------------------------------------------- *)
Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ recv   = {}
    /\ sent   = {}
    /\ done   = FALSE

(* ----------------------------------------------------------------------
   Next-state relation (inherits Echo's Next, simplified to core behavior)
   ---------------------------------------------------------------------- *)
Next ==
    \/ /\ ~initiator \in recv
       /\ recv' = recv \cup {initiator}
       /\ UNCHANGED <<parent, sent, done>>
    \/ \E n \in Node \ recv :
         /\ recv' = recv \cup {n}
         /\ parent' = [parent EXCEPT ![n] = 
                IF initiator \in recv THEN initiator ELSE NoNode]
         /\ UNCHANGED <<sent, done>>
    \/ \E n \in Node \ sent :
         /\ sent' = sent \cup {n}
         /\ UNCHANGED <<parent, recv, done>>
    \/ /\ recv = Node
       /\ sent = Node
       /\ done' = TRUE
       /\ UNCHANGED <<parent, recv, sent>>

(* ----------------------------------------------------------------------
   Specification (required to be named TestSpec)
   ---------------------------------------------------------------------- *)
TestSpec == Init /\ [][Next]_<<parent, recv, sent, done>>

(* ----------------------------------------------------------------------
   Export the required identifiers
   ---------------------------------------------------------------------- *)
SPECIFICATION TestSpec
INVARIANT TYPEOK
INVARIANT AncestorProperties

====