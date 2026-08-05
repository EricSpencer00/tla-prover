---- MODULE Reachable ----
(***************************************************************************)
(* Reachable is a breadth-first search for the set of nodes reachable from  *)
(* a distinguished root node.  It implements a variant of Misra's algorithm    *)
(* in which the set of nodes already marked reachable and the frontier are     *)
(* allowed to overlap.  When the frontier becomes empty, the set of marked     *)
(* nodes is exactly the set of reachable nodes, so the algorithm terminates     *)
(* with a correct answer.                                                     *)
(***************************************************************************)
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssume == Root \in Nodes

Reachable == ReachableFrom({Root})

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "search"

SearchStep ==
  /\ pc = "search"
  /\ frontier # {}
  /\ \E v \in frontier :
       /\ marked' = IF v \in marked THEN marked ELSE marked \cup {v}
       /\ frontier' = IF v \in marked
                       THEN frontier \ {v}
                       ELSE frontier \cup Succ[v]
  /\ UNCHANGED pc

DoneStep ==
  /\ pc = "search"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED << marked, frontier >>

\* Infinite stuttering once the computation has finished.
Terminate == pc = "done" /\ UNCHANGED vars

Next == SearchStep \/ DoneStep \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(SearchStep) /\ WF_vars(DoneStep)

Termination == <>(pc = "done")

TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in {"search", "done"}
  /\ (pc = "done") => frontier = {}

Inv1 == \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 == (marked \cup ReachableFrom(frontier)) = ReachableFrom(marked \cup frontier)

Inv3 == Reachable = marked \cup ReachableFrom(frontier)

TypeOK => []Inv1 /\ []Inv2 /\ []Inv3

PartialCorrectness == (pc = "done") => (marked = Reachable)

THEOREM Spec => []PartialCorrectness

(***************************************************************************)
(* Reachability is only guaranteed to fail when the reachable set is        *)
(* infinite, so termination is a liveness property that requires fairness.  *)
(***************************************************************************)
THEOREM ASSUME IsFiniteSet(Reachable) PROVE Spec => <>(pc = "done")

====