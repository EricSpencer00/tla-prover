---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ

\*--------------------------------------------------------------------
\* State variables
\*--------------------------------------------------------------------
VARIABLES marked, frontier, pc

\*--------------------------------------------------------------------
\* Helper definitions
\*--------------------------------------------------------------------
\* Relation representing the edge set of the graph
Rel == { <<n,m>> : n \in Nodes /\ m \in Succ[n] }

\* Nodes reachable (by any finite path) from a set S of nodes
Reach(S) == 
  S \cup { y \in Nodes : \E x \in S : <<x,y>> \in TC(Rel) }

\*--------------------------------------------------------------------
\* Operators required by the .cfg file
\*--------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]      \* placeholder for the substituted operator

LimitedSeq(S) == Seq(S)                     \* finite sequences for model checking

\*--------------------------------------------------------------------
\* Invariants
\*--------------------------------------------------------------------
TypeOK == 
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"Run", "Done"}

Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 == marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 == Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness == 
  pc = "Done" => marked = Reach({Root})

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init == 
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Run"

\*--------------------------------------------------------------------
\* Next-state relation
\*--------------------------------------------------------------------
PickUnmarked ==
  \E n \in frontier :
    /\ n \notin marked
    /\ marked'   = marked \cup {n}
    /\ frontier' = frontier \cup Succ[n]
    /\ pc'       = pc

PickMarked ==
  \E n \in frontier :
    /\ n \in marked
    /\ frontier' = frontier \ {n}
    /\ marked'   = marked
    /\ pc'       = pc

Terminate ==
  /\ frontier = {}
  /\ pc = "Run"
  /\ pc' = "Done"
  /\ UNCHANGED <<marked, frontier>>

Next == PickUnmarked \/ PickMarked \/ Terminate

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Vars == <<marked, frontier, pc>>

Spec == Init /\ [][Next]_Vars

\*--------------------------------------------------------------------
\* Liveness property
\*--------------------------------------------------------------------
Termination == <> (pc = "Done")
====