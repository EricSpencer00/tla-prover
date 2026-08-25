---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Sequences, TLC
EXTENDS ReachabilityAlgorithm, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

INIT ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"

(* Placeholder for the successor function supplied by the algorithm module. *)
Successors(n) == Succ[n]

NEXT ==
    \/ /\ pc = "run"
       /\ \E n \in frontier:
            /\ marked' = marked \cup {n}
            /\ frontier' = (frontier \ {n}) \cup (Successors(n) \ marked)
            /\ pc' = "run"
    \/ /\ pc = "run"
       /\ frontier = {}
       /\ pc' = "done"
       /\ UNCHANGED <<marked, frontier>>
    \/ /\ pc = "done"
       /\ UNCHANGED <<marked, frontier, pc>>

(* Invariant 1: type correctness and successor condition *)
Inv1 ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A n \in marked : Successors(n) \subseteq marked \cup frontier

(* Invariant 2: marked ∪ Reach(frontier) = Reach(marked ∪ frontier) *)
Inv2 ==
    LET Reach(S) ==
            { m \in Nodes : \E p \in Seq(Nodes) :
                /\ Len(p) > 0
                /\ p[1] = Root
                /\ p[Len(p)] = m
                /\ \A i \in 1..Len(p)-1 : p[i+1] \in Successors(p[i])
            }
    IN
        marked \cup Reach(frontier) = Reach(marked \cup frontier)

(* Invariant 3: Reach({Root}) = marked ∪ Reach(frontier) *)
Inv3 ==
    LET Reach(S) ==
            { m \in Nodes : \E p \in Seq(Nodes) :
                /\ Len(p) > 0
                /\ p[1] = Root
                /\ p[Len(p)] = m
                /\ \A i \in 1..Len(p)-1 : p[i+1] \in Successors(p[i])
            }
    IN
        Reach({Root}) = marked \cup Reach(frontier)

INVARIANTS == Inv1 /\ Inv2 /\ Inv3

(* Partial‑correctness property: when the algorithm terminates, marked equals the reachable set. *)
PROPERTIES ==
    /\ pc = "done"
    => marked =
        { m \in Nodes : \E p \in Seq(Nodes) :
            /\ Len(p) > 0
            /\ p[1] = Root
            /\ p[Len(p)] = m
            /\ \A i \in 1..Len(p)-1 : p[i+1] \in Successors(p[i])
        }

Spec == INIT /\ [][NEXT]_<<marked, frontier, pc>>
====