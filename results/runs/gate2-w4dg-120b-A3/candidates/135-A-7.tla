---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

\* The configuration module for the sequential Misra reachability algorithm.
\* It supplies the concrete graph structure and a bounded sequence type
\* (LimitedSeq) that model checking requires; the rest of the algorithm
\* -- its actions and the main invariants -- are imported from the standard
\* specification.

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "running", "done"}

\* Breadth-first marking: push the successors of the frontier, and pull them
\* into the frontier for the next step. The graph is directed, but the
\* invariant only cares about reachability, not about who is reachable from
\* whom, so every directed edge counts equally.
Step ==
  \/ /\ pc = "init"
     /\ frontier' = {Root}
     /\ marked' = {}
     /\ pc' = "running"
  \/ /\ pc = "running"
     /\ frontier' = {}
     /\ marked' = marked \cup frontier
     /\ \E b \in LimitedSeq(Nodes) :
          /\ b # << >>
          /\ b[1] \in frontier
          /\ \A i \in DOMAIN b : b[i] \in Succ
     /\ pc' = "running"
     /\ (IF frontier = {} THEN "done" ELSE "running")
  \/ /\ pc = "done"
     /\ UNCHANGED vars

Init == Step

Next == Step

Spec == Init /\ [][Next]_vars

\* The reachable set is exactly the set of nodes that show up somewhere in
\* some finite walk from the root, which is what the model checking is
\* actually proving (invariant, not a property) -- it is the core of the
\* algorithm's correctness and must hold in the initial state too.
Inv1 == marked = { n \in Nodes : \E s \in LimitedSeq(Nodes) : s # << >> /\ Head(s) = Root /\ n \in s }

Inv2 == frontier \subseteq Nodes \ {Root} /\ frontier \cap marked = {}

Inv3 == frontier \cup marked = { n \in Nodes : \E s \in LimitedSeq(Nodes) : s # << >> /\ Head(s) = Root /\ n \in s }

PartialCorrectness == Root \in marked

Termination == <>(pc = "done")

\* The graph structure the .cfg expects: every node points to exactly two
\* successors, chosen here as the next two nodes on the cycle.
ConnectedToSomeButNotAll == \E x \in Nodes : Succ = { (x + 1) % 4, (x + 2) % 4 }

\* The .cfg replaces Seq with this bounded version, so it is finite and
\* model checking can enumerate it; every entry must still be a graph node.
LimitedSeq == { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

====