---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, ConnectedToSomeButNotAll

ASSUME Root \in Nodes

\* Misra's visited/frontier overlap: Marked is the permanent visited set, Frontier
\* holds nodes still being explored and may contain already-marked nodes.
VARIABLES Marked, Frontier, Phase

vars == <<Marked, Frontier, Phase>>

Terminated == Phase = "done"

TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ Phase \in {"running", "done"}

Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ Phase = "running"

\* The main action: pick any frontier node, marked or not, nondeterministically.
Explore ==
  /\ Phase = "running"
  /\ \E n \in Frontier :
       \/ n \notin Marked
          /\ Marked' = Marked \cup {n}
          /\ Frontier' = Frontier \cup ConnectedToSomeButNotAll[n]
       \/ n \in Marked
          /\ Frontier' = Frontier \ {n}
  /\ Phase' = IF Frontier = {} THEN "done" ELSE Phase

Spec == Init /\ [][Explore]_vars

\* SAFETY: partial correctness via three reachability-split invariants.
\* The first two are the per-step form; the third is the unfolded union-of-two
\* sets characterization of Reachable from the root.
Reachable(n) ==
  /\ n \in Marked
  \/ (\E m \in Frontier : n \in ConnectedToSomeButNotAll[m])

Inv1 == \A n \in Marked : ConnectedToSomeButNotAll[n] \subseteq (Marked \cup Frontier)
Inv2 == \A n \in Frontier : ConnectedToSomeButNotAll[n] \subseteq (Marked \cup Frontier)
Inv3 == Reachable(Root) = (Marked \cup {n \in Nodes : \E m \in Frontier : n \in ConnectedToSomeButNotAll[m]})

PartialCorrectness == Reachable(Root) = Marked

Liveness ==
  /\ (\E f \in [Nodes -> SUBSET Nodes] : f = ConnectedToSomeButNotAll)
  /\ WF_vars(Explore)

====