---- MODULE MCEcho ----
EXTENDS Naturals

\* Model configuration for the Echo spanning tree algorithm.  This module
\* defines exactly the identifiers named in the .cfg: the constants
\* (Node, initiator, R, NoNode), the overriding operators (N1, I1, R1),
\* the standard Echo operators (Init, Next), and the invariants the .cfg
\* references (TypeOK, AncestorProperties).  A test variant that prints
\* the graph adjacency relation at startup is included but never becomes
\* reachable in a normal run.
CONSTANTS Node, initiator, R, NoNode

ASSUME NoNode \notin Node

\* Operators that the .cfg file substitutes; they are overridden at runtime
\* but must exist in every configuration of this module.
N1 == Node
I1 == initiator
R1 == R

VARIABLES parent, discovered, reported, noisy

vars == <<parent, discovered, reported, noisy>>

TypeOK ==
  /\ parent \in [N1 -> N1 \cup {NoNode}]
  /\ discovered \in [N1 -> BOOLEAN]
  /\ reported \in [N1 -> BOOLEAN]
  /\ noisy \in [N1 -> BOOLEAN]

Init ==
  /\ parent = [n \in N1 |-> NoNode]
  /\ discovered = [n \in N1 |-> FALSE]
  /\ reported = [n \in N1 |-> FALSE]
  /\ noisy = [n \in N1 |-> FALSE]

Discover ==
  /\ \E u \in N1, v \in N1 :
       /\ u # v
       /\ <<u, v>> \in R1
       /\ IF discovered[u] THEN ~discovered[v] ELSE discovered[v]
       /\ discovered' = [discovered EXCEPT ![v] = TRUE]
  /\ UNCHANGED <<parent, reported, noisy>>

Report ==
  /\ \E u \in N1, v \in N1 :
       /\ u # v
       /\ <<u, v>> \in R1
       /\ discovered[u] /\ ~discovered[v]
       /\ ~reported[u]
       /\ parent' = [parent EXCEPT ![v] = u]
       /\ reported' = [reported EXCEPT ![u] = TRUE]
  /\ UNCHANGED <<discovered, noisy>>

Terminate ==
  /\ \A n \in N1 : discovered[n]
  /\ UNCHANGED <<parent, discovered, reported, noisy>>

Next == Discover \/ Report \/ Terminate

TestPrint ==
  /\ \E msg \in {"init"} :
       /\ msg = "init"
       /\ (UNION { n \in Node : { {n, m} : m \in Node } }) = R
       /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* A variant of the spec whose only reachable state is the Init state, so
\* the print action is never actually reachable during a normal run.
TestSpec == Spec /\ TestPrint

AncestorProperties ==
  /\ initiator \in N1
  /\ \A n \in N1 : n # initiator => (parent[n] = NoNode <=> n = initiator)
  /\ \A n1, n2 \in N1 : (parent[n1] = n2 /\ n2 # NoNode) => parent[n2] # n1

====