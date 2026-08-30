---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

(* Model-checking configuration for the sequential Misra reachability       *)
(* algorithm.  It provides a concrete finite graph of 4 nodes, each with     *)
(* exactly two successors, and a bounded replacement for the infinite       *)
(* sequence (path) type used in the algorithm's reachability definition.    *)

CONSTANTS Nodes, Root, Succ

\* Reachability defined as an existential over finite sequences of nodes.
\* The override below (LimitedSeq) turns the infinite Seq into a bounded
\* sequence so the model stays finite.
RECURSIVE Reachable(_)
Reachable(n) ==
  \/ n = Root
  \/ \E k \in 1..Cardinality(Nodes) : \E s \in LimitedSeq([1..k -> Nodes]) :
        /\ s[1] = Root
        /\ s[k] = n
        /\ \A i \in 1..(k - 1) : ConnectedToSomeButNotAll(s[i], s[i + 1])

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "working", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "idle"

Start ==
  /\ pc = "idle"
  /\ pc' = "working"
  /\ frontier' = Succ(Root)
  /\ UNCHANGED marked

Mark(n) ==
  /\ pc = "working"
  /\ n \in frontier
  /\ n \notin marked
  /\ marked' = marked \cup {n}
  /\ frontier' = (frontier \cup Succ(n)) \ {n}
  /\ UNCHANGED pc

Drop(n) ==
  /\ pc = "working"
  /\ n \in frontier
  /\ n \in marked
  /\ frontier' = frontier \ {n}
  /\ UNCHANGED <<marked, pc>>

Finish ==
  /\ pc = "working"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ Start
  \/ \E n \in Nodes : Mark(n)
  \/ \E n \in Nodes : Drop(n)
  \/ Finish

Spec == Init /\ [][Next]_vars

(* Safety: type correctness and the three key invariants the algorithm     *)
(* maintains, plus partial correctness (all reachable nodes are marked).  *)
Inv1 == \A n \in frontier : n \notin marked
Inv2 == \A n \in Nodes : n \in marked => Reachable(n)
Inv3 == \A n \in Nodes : Reachable(n) => marked \cup frontier
PartialCorrectness == \A n \in Nodes : Reachable(n) => n \in marked

Termination == <>(pc = "done")

====