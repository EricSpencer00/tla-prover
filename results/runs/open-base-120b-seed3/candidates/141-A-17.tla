---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ

\* Operator that will be substituted for Succ by the .cfg
ConnectedToSomeButNotAll(node) == 
  IF node \in Nodes THEN {} ELSE {}

\* Finite version of Seq used by the .cfg in place of Seq
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= 10 }

VARIABLES marked, frontier, pc

\* Relation derived from the successor function
SuccRel == { <<n, m>> : n \in Nodes /\ m \in Succ[n] }

\* Reachability via transitive closure
Reach(S) == TC(SuccRel, S)

Init == 
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "run"

Next ==
  \/ /\ pc = "run"
     /\ frontier # {}
     /\ \E n \in frontier:
          IF n \notin marked THEN
            /\ marked'   = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
          ELSE
            /\ marked'   = marked
            /\ frontier' = frontier \ {n}
          /\ pc' = "run"
  \/ /\ pc = "run"
     /\ frontier = {}
     /\ pc' = "halt"
     /\ UNCHANGED <<marked, frontier>>
  \/ /\ pc = "halt"
     /\ UNCHANGED <<marked, frontier, pc>>

Spec == Init /\ [][Next]_<<marked, frontier, pc>> /\ WF_vars(Next)

TypeOK == 
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ Root \in Nodes

Inv1 == \A m \in marked : Succ[m] \subseteq marked \cup frontier

Inv2 == marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 == Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness == frontier = {} => marked = Reach({Root})

Termination == <> (frontier = {})

====