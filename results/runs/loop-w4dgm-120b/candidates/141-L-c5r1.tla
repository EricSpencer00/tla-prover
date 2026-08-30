---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

\* A node reachable from the frontier is reachable from the root only through
\* marked nodes or through the frontier itself -- overlap is allowed.
Inv1 ==
  \A n \in Nodes, m \in Nodes :
    (n \in marked /\ m \in Succ[n]) => (m \in marked \/ m \in frontier)

\* The marked set together with the frontier covers everything reachable from
\* their union, and nothing outside it is reachable from there.
Inv2 ==
  \A n \in Nodes :
    (n \in marked \/ n \in frontier) =>
      (\A m \in Nodes : (n \in marked \/ n \in frontier \/ m \in Succ[n]) => (m \in marked \/ m \in frontier))

\* Nodes reachable from the root are exactly the marked nodes plus whatever is
\* reachable from the frontier.
Inv3 ==
  \A n \in Nodes :
    (n \in frontier \/ \E m \in frontier : n \in Succ[m] \/ \E m \in frontier, k \in frontier : n \in Succ[Succ[m]]) <=> n \in marked

\* Marked nodes are exactly the nodes reachable from the root at termination.
PartialCorrectness ==
  /\ (\A n \in Nodes : n \in frontier => n \in marked \/ n \in frontier)
  /\ (\A n \in Nodes : (n \in marked \/ n \in frontier) => n \in marked \/ n \in frontier)
  /\ (\A n \in Nodes : n \in frontier \/ n \in marked => n \in marked \/ n \in frontier)

Termination ==
  (\A n \in Nodes : n \in frontier \/ n \in marked => n \in marked \/ n \in frontier) => \A n \in Nodes : n \in frontier => n \in marked

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

Explore ==
  /\ pc = "running"
  /\ frontier # {}
  /\ \E n \in frontier :
       \/ IF n \notin marked
          THEN /\ marked' = marked \cup {n}
               /\ frontier' = frontier \cup Succ[n]
          ELSE /\ marked' = marked
               /\ frontier' = frontier \ {n}
  /\ pc' = pc

AllDone ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ Explore
  \/ AllDone

Spec ==
  /\ Init
  /\ [][Next]_<<marked, frontier, pc>>
  /\ WF_vars(Explore)

====