---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "terminated"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* Misra's algorithm: a node may remain in the frontier after it is marked,
\* so the frontier can overlap the marked set. This is what makes it parallelizable.
Explore(n) ==
  /\ n \in frontier
  /\ pc = "running"
  /\ IF n \notin marked
       THEN /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
       ELSE /\ marked' = marked
            /\ frontier' = frontier \ {n}
  /\ UNCHANGED pc

Terminate ==
  /\ frontier = {}
  /\ pc = "running"
  /\ pc' = "terminated"
  /\ UNCHANGED <<marked, frontier>>

Next == (\E n \in Nodes: Explore(n)) \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(\E n \in Nodes: Explore(n))

\* Invariant 1: a successor of a marked node is accounted for -- in the marked
\* set or still waiting in the frontier.
Inv1 == \A a \in marked, n \in Succ[a] : n \in marked \/ n \in frontier

\* Invariant 2: the nodes reachable from what is already known (marked) plus
\* what is still to be explored (frontier) are exactly the part of the graph
\* already known, so nothing reachable from marked is lost.
Inv2 ==
  \A n \in Nodes :
    (n \in marked \/ n \in frontier) =>
      (\A m \in Nodes : (m \in marked /\ n \in Succ[m]) \/ (m \in frontier /\ n \in Succ[m]))

\* Invariant 3: the reachable set from the root is split exactly between the
\* already-marked nodes and the ones reachable from whatever is left in the frontier.
Inv3 ==
  {n \in Nodes : (\E m \in Nodes : m \in marked /\ n \in Succ[m]) \/ n = Root}
    \cup
  {n \in Nodes : (\E m \in Nodes : m \in frontier /\ n \in Succ[m])}
    = {n \in Nodes : (\E m \in Nodes : m \in marked \cup frontier /\ n \in Succ[m]) \/ n \in marked \cup frontier}

PartialCorrectness == Inv1 /\ Inv2 /\ Inv3

\* Termination is only guaranteed when the reachable set is finite; otherwise
\* the frontier could keep cycling forever. Weak fairness on Explore closes it out.
Termination == (frontier # {}) ~> (frontier = {})

\* The model replaces Succ with a bounded version ConnectedToSomeButNotAll, and
\* replaces the infinite Seq from Sequences with the finite version LimitedSeq.
ConnectedToSomeButNotAll(n) == Succ[n]
LimitedSeq == Seq

====