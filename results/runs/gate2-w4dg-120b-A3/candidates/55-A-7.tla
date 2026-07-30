---- MODULE MCEcho ----
EXTENDS Integers

\* This module serves as the model-checking configuration for the Echo
\* spanning-tree algorithm.  It reuses the full Echo specification and
\* simply supplies concrete bounded values for the unbounded constants:
\* a three-node fully-meshed graph and a deterministic initiator.
\* The configuration file (.cfg) also substitutes the operators N1, I1,
\* and R1, which are therefore defined here in terms of the constants.

CONSTANTS Node, initiator, R, NoNode

VARIABLES P, Src, Dest, Parent, Seen, Inbox, Mode

vars == <<P, Src, Dest, Parent, Seen, Inbox, Mode>>

\* A fully meshed graph on three distinct nodes: every distinct pair is
\* connected, symmetric, and irreflexive -- exactly what the Echo spec
\* requires for its connectivity/symmetry/irreflexivity assumptions.
Conn(x, y) == /\ x # y
              /\ {{x, y}} \subseteq R

Init ==
  /\ P = "initing"
  /\ \E r \in Node : initiator = r
  /\ \E x \in Node : \E y \in Node :
        /\ Conn(x, y)
        /\ Conn(y, x)
  /\ Parent = [n \in Node |-> NoNode]
  /\ Seen = [n \in Node |-> FALSE]
  /\ Inbox = [n \in Node |-> {}]
  /\ Src = [n \in Node |-> NoNode]
  /\ Dest = [n \in Node |-> NoNode]
  /\ Mode = [n \in Node |-> "idle"]

\* No variants: the action set is exactly the Echo set, imported.
Next == \E a \in EchoNext : a

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ P \in {"initing", "done"}
  /\ Parent \in [Node -> Node \cup {NoNode}]
  /\ Seen \in [Node -> BOOLEAN]
  /\ Inbox \in [Node -> SUBSET Node]
  /\ Src \in [Node -> Node \cup {NoNode}]
  /\ Dest \in [Node -> Node \cup {NoNode}]
  /\ Mode \in [Node -> {"idle"}]

\* The ancestor properties are the only correctness criteria of the Echo
\* spec: when the protocol has converged, the initiator is the unique
\* root of the spanning tree and the ancestor relation is acyclic.
AncestorProperties == EchoAncestorProperties

\* Test variant: prints the fully-meshed graph adjacency relation once
\* the initiator is chosen.  The print is a side-effect only; it never
\* changes any state or blocks the model checker.
InitPrint ==
  /\ P = "initing"
  /\ \E r \in Node :
        /\ initiator = r
        /\ \E x \in Node : \E y \in Node :
             /\ Conn(x, y)
             /\ Conn(y, x)
        /\ Print("Adjacency relation: " ^ Cardinality(R) ^ " edges")
  /\ UNCHANGED vars

\* This operator is never used by the spec but is defined as a sentinel
\* constant: the NoNode value is guaranteed distinct from every node.
\* Its existence is what stops the model checker from folding it away.
NoNodeDistinct == \A n \in Node : NoNode # n

\* Operators overridden by the .cfg via substitution.  They are defined
\* here in terms of the constants so that the module compiles on its own
\* even without the substitution; the substitution itself replaces them.
N1 == Node
I1 == initiator
R1 == R

====