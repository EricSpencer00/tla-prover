---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Nodes, Root

(* ---------------------------------------------------------------------- *)
(* State variables *)
VARIABLES Marked, Frontier, pc

(* ---------------------------------------------------------------------- *)
(* Helper definitions *)
Succ(n) == { y \in Nodes : <<n, y>> \in Edge }

Reachable(S) == TC(Edge, S)

(* ---------------------------------------------------------------------- *)
(* Initial state *)
INIT ==
    /\ Marked = {}
    /\ Frontier = {Root}
    /\ pc = "Start"
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes

(* ---------------------------------------------------------------------- *)
(* Actions *)
Expand ==
    \E n \in Frontier :
        /\ Marked' = Marked \cup {n}
        /\ Frontier' = (Frontier \ {n}) \cup (Succ(n) \ Marked)
        /\ pc' = pc
        /\ UNCHANGED <<>>

Done ==
    /\ Frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<Marked, Frontier>>

NEXT ==
    Expand \/ Done

(* ---------------------------------------------------------------------- *)
(* Invariants *)
Inv1 ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ pc \in {"Start", "Done"}
    /\ \A n \in Marked : Succ(n) \subseteq Marked \cup Frontier

Inv2 ==
    Marked \cup Reachable(Frontier) = Reachable(Marked \cup Frontier)

Inv3 ==
    Reachable({Root}) = Marked \cup Reachable(Frontier)

INVARIANTS == Inv1 /\ Inv2 /\ Inv3

(* ---------------------------------------------------------------------- *)
(* Partial correctness property *)
TerminationCorrectness ==
    (pc = "Done") => (Marked = Reachable({Root}))

PROPERTIES == TerminationCorrectness

(* ---------------------------------------------------------------------- *)
(* Specification *)
vars == <<Marked, Frontier, pc>>
Spec == INIT /\ [][NEXT]_vars

====