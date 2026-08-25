---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets, TLC, Temporal

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

(* --- Helper definitions --- *)
Edge == { <<n, m>> : n \in Nodes /\ m \in Succ[n] }

ReachableFromRoot == { n \in Nodes : <<Root, n>> \in TC(Edge) }

ReachOne(S) == UNION { Succ[x] : x \in S }

(* --- Initial state --- *)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Run"

(* --- Next-state relation --- *)
Next ==
  \/ /\ pc = "Run"
     /\ frontier # {}
     /\ LET n == CHOOSE x \in frontier : TRUE IN
        IF n \notin marked THEN
          /\ marked'   = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
        ELSE
          /\ marked'   = marked
          /\ frontier' = frontier \ {n}
        /\ pc' = "Run"
  \/ /\ pc = "Run"
     /\ frontier = {}
     /\ pc' = "Done"
  \/ /\ pc = "Done"
     /\ UNCHANGED <<marked, frontier, pc>>

Spec == Init /\ [][Next]_<<marked, frontier, pc>> /\ WF_vars(Next)

(* --- Invariants --- *)
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes

Inv1 == \A m \in marked : Succ[m] \subseteq marked \cup frontier

Inv2 == marked \cup ReachOne(frontier) = ReachOne(marked \cup frontier)

Inv3 == ReachableFromRoot = marked \cup ReachOne(frontier)

PartialCorrectness == [](frontier = {} => marked = ReachableFromRoot)

(* --- Liveness property --- *)
Termination == <> (frontier = {})

(* --- Operators overridden by the .cfg --- *)
ConnectedToSomeButNotAll(n) == Succ[n]

(* --- Replacement for Seq from Sequences --- *)
LimitedSeq(S) == {}

====