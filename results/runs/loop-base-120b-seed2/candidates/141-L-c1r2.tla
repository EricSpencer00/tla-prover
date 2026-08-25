---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Nodes, Root, RawSucc

(* The operator that the .cfg substitutes for Succ *)
ConnectedToSomeButNotAll == RawSucc

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

(* Initial state *)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"

(* Edge relation of the graph *)
Edge == { <<x, y>> : x \in Nodes /\ y \in ConnectedToSomeButNotAll[x] }

(* Reachability from a set of nodes, using the transitive closure operator TC
   provided by the TLC standard module. *)
Reach(S) == S \/ { y \in Nodes : \E x \in S : <<x, y>> \in TC(Edge) }

(* Main transition relation *)
Next ==
    \/ /\ pc = "run"
       /\ frontier # {}
       /\ \E n \in frontier :
            /\ IF n \notin marked
                  THEN /\ marked'   = marked \cup {n}
                       /\ frontier' = frontier \cup ConnectedToSomeButNotAll[n]
                  ELSE /\ marked'   = marked
                       /\ frontier' = frontier \ {n}
            /\ UNCHANGED pc
    \/ /\ pc = "run"
       /\ frontier = {}
       /\ pc' = "done"
       /\ UNCHANGED <<marked, frontier>>
    \/ /\ pc = "done"
       /\ UNCHANGED <<marked, frontier, pc>>

Spec == Init /\ [][Next]_vars

(* Type correctness invariant *)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ Root \in Nodes
    /\ pc \in {"run", "done"}
    /\ RawSucc \in [Nodes -> SUBSET Nodes]

(* Invariant 1: every successor of a marked node is either marked or in the frontier *)
Inv1 == \A m \in marked : ConnectedToSomeButNotAll[m] \subseteq marked \cup frontier

(* Invariant 2: the union of the marked set and the nodes reachable from the frontier
   equals the nodes reachable from the union of marked and frontier *)
Inv2 == marked \cup Reach(frontier) = Reach(marked \cup frontier)

(* Invariant 3: the reachable set from the root equals the marked set plus the
   nodes reachable from the frontier *)
Inv3 == Reach({Root}) = marked \cup Reach(frontier)

(* Partial correctness: when the algorithm terminates, the marked set is exactly
   the set of nodes reachable from the root *)
PartialCorrectness == (pc = "done") => (marked = Reach({Root}))

(* Liveness property: if the reachable set from the root is finite, the algorithm
   eventually terminates *)
Termination == [] ( (Finite(Reach({Root}))) => <> (pc = "done") )

====