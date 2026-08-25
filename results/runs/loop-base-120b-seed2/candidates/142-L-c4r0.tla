---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

(*--------------------------------------------------------------------
   Definitions
  --------------------------------------------------------------------*)

Vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Init"

Edge == [n \in Nodes, m \in Nodes |-> m \in Succ[n]]

ReachFrom(S) ==
    S \cup { y \in Nodes : \E x \in S : <<x, y>> \in TC(Edge) }

Inv1 ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Init", "Step", "Done"}
    /\ \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
    marked \cup ReachFrom(frontier) = ReachFrom(marked \cup frontier)

Inv3 ==
    ReachFrom({Root}) = marked \cup ReachFrom(frontier)

(*--------------------------------------------------------------------
   Actions
  --------------------------------------------------------------------*)

Expand ==
    /\ pc = "Step"
    /\ frontier # {}
    /\ \E n \in frontier :
        /\ marked' = marked \cup {n}
        /\ frontier' = (frontier \ {n}) \cup Succ[n]
        /\ pc' = "Step"

Done ==
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ (* first step: move from Init to Step *)
        /\ pc = "Init"
        /\ pc' = "Step"
        /\ UNCHANGED <<marked, frontier>>
    \/ Expand
    \/ Done

Spec ==
    Init /\ [][Next]_Vars

INVARIANTS ==
    Inv1 /\ Inv2 /\ Inv3

Final ==
    Spec => [] (frontier = {} => marked = ReachFrom({Root}))

PROPERTIES ==
    Final
====