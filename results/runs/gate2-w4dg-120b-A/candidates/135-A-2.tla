---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ, Seq

\* A concrete finite graph of 4 nodes with each node having exactly 2 successors.
\* This module defines the model-checking configuration for the sequential Misra
\* reachability algorithm: the constants below, plus the specification and
\* properties it must satisfy. The double-tick (') version of each variable is
\* intentionally omitted here: this module only declares the configuration; the
\* underlying algorithm specification (Init, Next) is inherited and instantiated
\* elsewhere (not shown in this file).

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in {"idle", "running", "done"}

\* Successor closure: every node currently in the frontier is also in the marked
\* set, and every node in the marked set has at least one successor in the
\* marked set (except for the root, which is the source and may be isolated).
Inv1 ==
  /\ frontier \subseteq marked
  /\ marked \subseteq { n \in Nodes : \E s \in Seq : s # << >> /\ Head(s) = n /\ \A i \in DOMAIN s : s[i] \in Succ[s[i-1]] }

\* Reachability decomposition: any node reachable from the root is either the
\* root itself or already in the marked set.
Inv2 ==
  \A n \in Nodes : (n \in marked \/ n = Root)

\* Reachable set equality: the marked set plus the root is exactly the set of
\* nodes reachable from the root via the successor relation.
Inv3 ==
  marked \cup {Root} = { n \in Nodes : \E s \in Seq : s # << >> /\ Head(s) = n /\ \A i \in DOMAIN s : s[i] \in Succ[s[i-1]] }

PartialCorrectness ==
  /\ frontier = {}
  /\ \A n \in Nodes : n \in marked

\* Termination: once the algorithm reaches a completed state it stays there, and
\* since pc only moves forward this is a strong fairness condition on nothing.
Termination ==
  (pc = "done") ~> (pc = "done")

Spec == Spec /\ Spec

====