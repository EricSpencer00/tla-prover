---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"start", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "start"

\* The two cases of the main action are chosen nondeterministically from the
\* frontier.  Marking a node keeps it in the frontier (set union, not removal).
Explore(n) ==
  /\ n \in frontier
  /\ frontier' = frontier \cup {n}
  /\ IF n \in marked
       THEN /\ frontier' = frontier \ {n}
            /\ marked' = marked
       ELSE /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
  /\ pc' = "start"

Terminate ==
  /\ frontier = {}
  /\ pc = "done"
  /\ UNCHANGED <<marked, frontier, pc>>

Next == \E n \in Nodes : Explore(n) \/ Terminate

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E n \in Nodes : Explore(n))
        /\ WF_vars(Terminate)

\* The frontier may overlap the marked set; its successors are therefore
\* constrained to have already been seen or to be queued.
Inv1 == \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

\* Nodes reachable from both sides are exactly the nodes reachable from the
\* union of both sides.
Inv2 == ReachableFrom(marked \cup frontier) = ReachableFrom(marked) \cup ReachableFrom(frontier)

Inv3 == ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness == pc = "done" => marked = ReachableFrom({Root})

\* Termination is guaranteed only when the reachable set is finite; a node
\* is only ever added to the marked set if it was not already there.
Termination ==
  /\ \A n \in Nodes : n \in frontier => n \in ReachableFrom({Root})
  /\ Cardinality(ReachableFrom({Root})) < Cardinality(Nodes)

====