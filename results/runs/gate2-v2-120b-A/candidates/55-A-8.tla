---------------- MODULE MCEcho ----------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANT Node, initiator, R, NoNode

(*--------------------------------------------------------------------
  Derived constants
--------------------------------------------------------------------*)
NodeSet == Node          \* convenience alias

(*--------------------------------------------------------------------
  State variables (mirroring those of the Echo specification)
--------------------------------------------------------------------*)
VARIABLES
    parent,   \* [Node -> Node \cup {NoNode}]
    children, \* [Node -> SUBSET Node]
    received, \* [Node -> BOOLEAN]
    done      \* [Node -> BOOLEAN]   \* true when node has terminated

(*--------------------------------------------------------------------
  Type correctness (for illustration; actual TypeOK invariant defined later)
--------------------------------------------------------------------*)
TypeOK ==
    /\ parent \in [Node -> (Node \cup {NoNode})]
    /\ children \in [Node -> SUBSET Node]
    /\ received \in [Node -> BOOLEAN]
    /\ done \in [Node -> BOOLEAN]
    /\ NoNode \notin Node

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ children = [n \in Node |-> {}]
    /\ received = [n \in Node |-> FALSE]
    /\ done = [n \in Node |-> FALSE]
    /\ received[initiator] = TRUE   \* initiator starts with the message

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
Neighbors(n) == { m \in Node : <<n, m>> \in R }

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
Send(n) ==
    /\ ~done[n]
    /\ received[n]
    /\ \E m \in Neighbors(n) :
        /\ ~received[m]
        /\ parent' = [parent EXCEPT ![m] = n]
        /\ children' = [children EXCEPT ![n] = children[n] \cup {m}]
        /\ received' = [received EXCEPT ![m] = TRUE]
        /\ UNCHANGED <<done>>

Terminate(n) ==
    /\ ~done[n]
    /\ \A m \in Neighbors(n) : received[m] \/ done[m]   \* all neighbors have been heard from
    /\ done' = [done EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<parent, children, received>>

Next ==
    \/ \E n \in Node : Send(n)
    \/ \E n \in Node : Terminate(n)

(*--------------------------------------------------------------------
  Specification (TestSpec) and termination condition
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<parent, children, received, done>>

Termination == \A n \in Node : done[n]

(*--------------------------------------------------------------------
  Safety invariant: AncestorProperties
  - The ancestor relation defined by parent is acyclic.
  - The initiator is an ancestor of every other node (or has no parent).
--------------------------------------------------------------------*)
Ancestor(n) ==
    IF parent[n] = NoNode THEN {}
    ELSE {parent[n]} \cup Ancestor(parent[n])

AncestorProperties ==
    /\ \A n \in Node : n \notin Ancestor(n)               \* acyclicity
    /\ \A n \in Node : n = initiator \/ initiator \in Ancestor(n)

(*--------------------------------------------------------------------
  Exported identifiers required by the .cfg
--------------------------------------------------------------------*)
TestSpec == Spec
Init == Init
Next == Next
TypeOK == TypeOK
AncestorProperties == AncestorProperties

=============================================================================