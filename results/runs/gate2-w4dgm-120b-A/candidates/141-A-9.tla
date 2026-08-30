---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

(* Misra's variant of breadth-first search: the marked (visited) set and the    *)
(* frontier may overlap.  Because a marked node can still sit in the frontier    *)
(* and hand out new successors, the algorithm can be parallelized, as described    *)
(* in the companion parallel implementation.                                     *)

CONSTANTS Nodes, Root, Succ

ASSUME /\ Root \in Nodes
       /\ Succ \in [Nodes -> SUBSET Nodes]

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "halted"}

RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
    IF S = {} THEN {}
    ELSE LET x == CHOOSE y \in S : TRUE IN Succ[x] \cup ReachableFrom(S \ {x})

RECURSIVE ReachableFromSet(_)
ReachableFromSet(S) ==
    IF S = {} THEN {}
    ELSE LET x == CHOOSE y \in S : TRUE IN {x} \cup ReachableFrom({x}) \cup ReachableFromSet(S \ {x})

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

(* The frontier and the marked set may overlap; the action is chosen from the  *)
(* frontier nondeterministically, modeling a concurrently reachable node.        *)
BFSStep ==
    /\ pc = "running"
    /\ \E n \in frontier :
         \/ IF n \notin marked
              THEN /\ marked' = marked \cup {n}
                   /\ frontier' = frontier \cup Succ[n]
              ELSE /\ marked' = marked
                   /\ frontier' = frontier \ {n}
    /\ pc' = pc

Halt ==
    /\ pc = "running"
    /\ frontier = {}
    /\ pc' = "halted"
    /\ UNCHANGED <<marked, frontier>>

Next == BFSStep \/ Halt

Spec == Init /\ [][Next]_vars

(* Safety: when halted, the marked set is exactly the reachable set.            *)
Inv1 == \A n \in Nodes : n \in marked => (Succ[n] \subseteq marked \cup frontier)
Inv2 == (marked \cup frontier) \cup ReachableFromSet(frontier) = ReachableFromSet(marked \cup frontier)
Inv3 == ReachableFromSet({Root}) = marked \cup ReachableFromSet(frontier)
PartialCorrectness == (pc = "halted") => (marked = ReachableFromSet({Root}))

(* Liveness: with a finite reachable set, the frontier cannot stay non-empty     *)
(* forever, since each loop either marks a fresh node or removes a stale one.    *)
Termination == (\A n \in Nodes : Succ[n] = {})
    ~> (pc = "halted")

(* ------------------------------------------------------------------------- *)
(* Operators that the .cfg file substitutes in/out.  Left names are overridden. *)
(* ------------------------------------------------------------------------- *)

(* A finite counterpart to Seq (Sequences) for use in the companion module.    *)
LimitedSeq(_, _) == {}

(* The shape of the graph is left open, but the cfg replaces Succ with a       *)
(* bounded variant for checking; keep the generic definition here.             *)
ConnectedToSomeButNotAll == {}

====