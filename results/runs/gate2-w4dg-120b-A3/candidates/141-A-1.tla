---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

\* The algorithm keeps the visited and frontier sets separate even though they
\* may overlap (the key Misra variant). p is the program counter for the
\* single process; Terminate is the state where the loop has finished.
VARIABLES visited, frontier, p

vars == << visited, frontier, p >>

\* Weak fairness on the single loop action is what forces progress: with a
\* finite reachable set the frontier cannot be left non-empty forever.
TypeOK ==
  /\ visited \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ p \in {"Running", "Terminate"}

Init ==
  /\ visited = {}
  /\ frontier = {Root}
  /\ p = "Running"

Shoot(node) ==
  /\ node \in frontier
  /\ visited' = visited \cup {node}
  /\ frontier' = frontier \cup Succ[node]
  /\ UNCHANGED p

Drop(node) ==
  /\ node \in frontier
  /\ node \in visited
  /\ frontier' = frontier \ {node}
  /\ UNCHANGED << visited, p >>

MainLoop ==
  /\ p = "Running"
  /\ \E node \in frontier :
       \/ Shoot(node)
       \/ Drop(node)

Terminate ==
  /\ p = "Running"
  /\ frontier = {}
  /\ p' = "Terminate"
  /\ UNCHANGED << visited, frontier >>

Next == MainLoop \/ Terminate

Spec == Init /\ [][Next]_vars
    /\ WF_vars(MainLoop)
    /\ WF_vars(Terminate)

\* Safety: every reachable node is either in visited or in frontier. The three
\* invariants together resolve the overlap, and the last is the actual partial
\* correctness claim.
Inv1 ==
  \A x \in visited : Succ[x] \subseteq (visited \cup frontier)

Inv2 ==
  (visited \cup frontier) \subseteq ReachableFrom(Nodes, visited \cup frontier)

Inv3 ==
  (Nodes \ visited) \subseteq ReachableFrom(Nodes, frontier)

PartialCorrectness ==
  visited = ReachableFrom(Nodes, {Root})

Termination == (p = "Running") ~> (p = "Terminate")

\* Operators that the .cfg file substitutes: Succ is left as a constant, and
\* the operator on the right is what the name on the left will mean.
ConnectedToSomeButNotAll(x) == IF Succ[x] = {} THEN {} ELSE Succ[x]

\* Limiting the built-in Seq operator to a finite subset (a calibration
\* artifact of the .cfg file) while keeping the full Sequences extension.
LimitedSeq(s) == SelectSeq(s, \A i \in DOMAIN s : s[i] \in Nodes)

====