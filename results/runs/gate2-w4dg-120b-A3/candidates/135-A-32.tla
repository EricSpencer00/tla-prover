---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

\* The configuration module redefines the Succ operator to a finite version of
\* "connected to some but not all", and redefines Seq to a bounded version so
\* the model is checkable. The left-hand names (Succ, Seq) are replaced by the
\* right-hand operators in the .cfg, so only the right-hand operators are
\* declared here and the left-hand names are never redefined.

\* ConnectedToSomeButNotAll is substituted for Succ in the .cfg, so Succ
\* resolves to this bounded, finite version at verification time.
ConnectedToSomeButNotAll(n) == { m \in Nodes : n # m }

\* A bounded version of Sequences' Seq: FINITE Seq, so the model stays finite
\* even though the reachability definition quantifies over paths (sequences).
LimitedSeq(S) == { f \in [1..Cardinality(S) -> S] : \A i \in 1..Cardinality(S) : f[i] \in S }

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "running", "done"}

\* Successor closure: every node in the marked set has all its Succ successors
\* (per the .cfg substitution) in the marked set.
Inv1 ==
    \A n \in marked : ConnectedToSomeButNotAll(n) \subseteq marked

\* Reachability decomposition: the marked set is exactly the set of nodes
\* reachable from the root via a sequence, using the bounded sequence set.
Inv2 ==
    marked = { n \in Nodes : \E s \in LimitedSeq(Nodes) : s[1] = Root /\ s[Cardinality(s)] = n }

\* The frontier set is exactly the successors of the current frontier, filtered
\* by reachability from the root using the bounded sequence set.
Inv3 ==
    frontier = { n \in Nodes : \E m \in frontier : n \in ConnectedToSomeButNotAll(m) /\ \E s \in LimitedSeq(Nodes) : s[1] = Root /\ s[Cardinality(s)] = n }

PartialCorrectness ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes

Init ==
    /\ marked = { Root }
    /\ frontier = { Root }
    /\ pc = "idle"

Explore ==
    /\ pc = "idle"
    /\ pc' = "running"
    /\ UNCHANGED << marked, frontier >>

ExpandFrontier ==
    /\ pc = "running"
    /\ frontier # {}
    /\ marked' = marked \cup { n \in Nodes : \E m \in frontier : n \in ConnectedToSomeButNotAll(m) }
    /\ frontier' = { n \in Nodes : \E m \in frontier : n \in ConnectedToSomeButNotAll(m) }
    /\ UNCHANGED pc

Complete ==
    /\ pc = "running"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED << marked, frontier >>

Spec == Init /\ [][Explore \/ ExpandFrontier \/ Complete]_vars

Termination == <>(pc = "done")

====