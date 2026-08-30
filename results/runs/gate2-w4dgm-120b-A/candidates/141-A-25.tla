---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

(* Misra's reachable-node algorithm: a two-case action where the visited    *)
(* set and the frontier may overlap, chosen for a parallelizable variant.  *)
(* It is parameterized by a root node and a neighbour function Succ.         *)

CONSTANTS Nodes, Root, Succ

ASSUME /\ Root \in Nodes
       /\ Succ \in [Nodes -> SUBSET Nodes]

VARIABLES visited, frontier, pc

vars == <<visited, frontier, pc>>

Bump == IF pc = "start" THEN "mid" ELSE "start"

TypeOK ==
    /\ visited \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"start", "mid"}

Init ==
    /\ visited = {}
    /\ frontier = {Root}
    /\ pc = "start"

\* The two cases, applied to an arbitrary frontier node so the action stays
\* weakly fair even when some frontier nodes are already visited.
Explore ==
    /\ \E n \in frontier :
         /\ IF n \notin visited
              THEN /\ visited' = visited \cup {n}
                   /\ frontier' = frontier \cup Succ[n]
              ELSE /\ visited' = visited
                   /\ frontier' = frontier \ {n}
    /\ pc' = Bump

Terminate ==
    /\ frontier = {}
    /\ pc' = pc
    /\ visited' = visited
    /\ frontier' = frontier

Next == Explore \/ Terminate

Spec == Init /\ [][Next]_vars /\ SF_vars(Explore)

(* Every successor of a visited node is either already visited or still in  *)
(* the frontier, so no reachable node can fall outside visited \cup frontier. *)
Inv1 == \A n \in visited : \A s \in Succ[n] : s \in visited \/ s \in frontier

(* The reachable nodes from marked plus those reachable from the frontier   *)
(* together are exactly the reachable nodes from their union.               *)
Inv2 == ReachableFrom(visited \cup frontier) = visited \cup ReachableFrom(frontier)

(* Once the frontier empties, visited is exactly the reachable set.          *)
Inv3 == (frontier = {}) => (visited = ReachableFrom({Root}))

PartialCorrectness == visited = ReachableFrom({Root})

Termination == (\A n \in Nodes : \E k \in Nat : n \in ReachableFrom({n}) => k \in Nat)
                  ~> (frontier = {})

(* The cfg file replaces the name Succ with ConnectedToSomeButNotAll and    *)
(* Seq with a bounded version of itself; the definitions here are the       *)
(* unbounded originals so the substitution can take effect at checking time. *)
ConnectedToSomeButNotAll == Succ
LimitedSeq == Seq

ReachableFrom(S) ==
    {n \in Nodes : \E k \in Nat : \E t \in LimitedSeq(Nodes) :
        /\ Len(t) = k
        /\ t[1] \in S
        /\ \A i \in 1 .. (k - 1) : t[i + 1] \in ConnectedToSomeButNotAll[t[i]]}

====