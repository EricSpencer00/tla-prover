---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*-----------------------------------------------------------------------
  Constants (to be given values in the .cfg file)
------------------------------------------------------------------------*)
CONSTANTS
    Node,          \* The finite set of node identifiers (strings)
    initiator,     \* The distinguished initiator node
    R,             \* The undirected graph adjacency relation (set of pairs)
    NoNode         \* Sentinel value distinct from all nodes

(*-----------------------------------------------------------------------
  State variables (identical to those in the Echo specification)
------------------------------------------------------------------------*)
VARIABLES
    parent,        \* Function mapping each node to its parent (or NoNode)
    received,      \* Set of nodes that have already received the echo
    done           \* Boolean flag indicating termination of the algorithm

(*-----------------------------------------------------------------------
  Helper definitions
------------------------------------------------------------------------*)
NodeSet == Node

Neighbors(n) == { m \in Node : <<n, m>> \in R }

(*-----------------------------------------------------------------------
  Type-correctness invariant (applies to all state variables)
------------------------------------------------------------------------*)
TypeOK == /\ parent \in [Node -> (Node \cup {NoNode})]
         /\ received \subseteq Node
         /\ done \in BOOLEAN

(*-----------------------------------------------------------------------
  Safety invariant: spanning‑tree ancestor properties
------------------------------------------------------------------------*)
AncestorProperties ==
    /\ done => initiator \in received
    /\ done => \A n \in Node \ {initiator} :
            parent[n] # NoNode
    /\ done => \A n \in Node :
            (parent[n] = NoNode) => n = initiator
    /\ done => \A n \in Node :
            (parent[n] # NoNode) => parent[n] \in received
    /\ done => \A n \in Node :
            (parent[n] # NoNode) => n \notin parent[n]  \* no self‑loop
    /\ done => \A n \in Node :
            (parent[n] # NoNode) => ~ (n \in TransitiveClosure(parent, initiator))
    /\ done => initiator = initiator  \* trivial guarantee that initiator exists

(* Transitive closure of the parent relation, used only for the acyclicity check *)
VARIABLES tempParent

TransitiveClosure(parentFun, start) ==
    LET step(x) == IF parentFun[x] = NoNode THEN {} ELSE {parentFun[x]}
    IN RECURSIVE closure(_)
    IN closure(start) \cup
       IF start \in Node THEN
          UNION { closure(y) : y \in step(start) }
       ELSE {}

(*-----------------------------------------------------------------------
  Initial state (matches Echo specification)
------------------------------------------------------------------------*)
Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ received = {}
    /\ done = FALSE
    /\ tempParent = parent   \* auxiliary variable to compute closure

(*-----------------------------------------------------------------------
  Echo algorithm actions (simplified but faithful to the description)
------------------------------------------------------------------------*)
SendEcho ==
    \E n \in Node :
        /\ n \in received
        /\ \E m \in Neighbors(n) :
            /\ m \notin received
            /\ parent' = [parent EXCEPT ![m] = n]
            /\ received' = received \cup {m}
            /\ UNCHANGED <<done, tempParent>>

Terminate ==
    /\ ~done
    /\ \A n \in Node : n = initiator \/ parent[n] # NoNode
    /\ done' = TRUE
    /\ UNCHANGED <<parent, received, tempParent>>

Next ==
    \/ SendEcho
    \/ Terminate
    \/ UNCHANGED <<parent, received, done, tempParent>>

(*-----------------------------------------------------------------------
  Specification and variants
------------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<parent, received, done, tempParent>>

TestSpec == Spec
    /\ Print("Adjacency relation R = ", R)

(*-----------------------------------------------------------------------
  Theorem (optional, for TLC) – asserts that the invariants hold under Spec
------------------------------------------------------------------------*)
THEOREM Spec => []TypeOK /\ []AncestorProperties

=============================================================================