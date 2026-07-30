---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

\* reachable(v) is the set of nodes reachable from a node v via the graph's
\* successor relation; it's used in the correctness argument below.
RECURSIVE reachable(_)
reachable(v) ==
  {v} \cup (IF v \in Nodes THEN UNION {reachable(w) : w \in Succ[v]} ELSE {})

VARIABLES explored, frontier, pc

vars == <<explored, frontier, pc>>

TypeOK ==
  /\ explored \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"run", "halt"}

Init ==
  /\ explored = {}
  /\ frontier = {Root}
  /\ pc = "run"

\* The main action of Misra's algorithm, with its two nondeterministic cases.
Step ==
  /\ pc = "run"
  /\ \E v \in frontier :
       /\ IF v \notin explored
          THEN /\ explored' = explored \cup {v}
               /\ frontier' = frontier \cup Succ[v]
          ELSE /\ explored' = explored
               /\ frontier' = frontier \ {v}
  /\ pc' = "run"

Terminate ==
  /\ pc = "run"
  /\ frontier = {}
  /\ pc' = "halt"
  /\ UNCHANGED <<explored, frontier>>

Next == Step \/ Terminate

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Step)
        /\ WF_vars(Terminate)

\* Invariant (1): every successor of a marked node is either already marked
\* or waiting in the frontier -- the frontier and the explored set together
\* contain the expanding wavefront of reachable nodes.
Inv1 == \A v \in explored, u \in Succ[v] : u \in explored \/ u \in frontier

\* Invariant (2): the union of explored nodes and nodes reachable from the
\* frontier is exactly the set reachable from their union.
Inv2 == reachable(explored \cup frontier) = explored \cup reachable(frontier)

\* Invariant (3): reachable from the root is exactly explored plus reachable
\* from the frontier; this is what lets the overlap occur without loss.
Inv3 == reachable(Root) = explored \cup reachable(frontier)

PartialCorrectness == (pc = "halt") => (explored = reachable(Root))

Termination == (pc = "run") ~> (pc = "halt")

====