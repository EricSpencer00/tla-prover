---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, SeqReachAlg, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

(*-----------------------------------------------------------------
  Initial state : start with only the root marked, empty frontier,
  and a program counter at the initial location.
-----------------------------------------------------------------*)
Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "init"

(*-----------------------------------------------------------------
  Next : placeholder for the algorithm's transition relation.
  The real actions are imported from SeqReachAlg; here we just
  provide a stub so the specification is syntactically complete.
-----------------------------------------------------------------*)
Next ==
    \/ /\ pc = "init"
       /\ pc' = "step"
       /\ UNCHANGED <<marked, frontier>>
    \/ /\ pc = "step"
       /\ pc' = "done"
       /\ UNCHANGED <<marked, frontier>>
    \/ /\ pc = "done"
       /\ UNCHANGED <<marked, frontier, pc>>

vars == <<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Invariant 1 : type correctness and the successor property.
-----------------------------------------------------------------*)
Inv1 ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A n \in marked : Succ[n] \subseteq marked \cup frontier

(*-----------------------------------------------------------------
  Invariant 2 : relationship between marked + reachable from frontier
  and reachable from their union.
-----------------------------------------------------------------*)
Inv2 ==
    (marked \cup ReachFrom(frontier)) = ReachFrom(marked \cup frontier)

(*-----------------------------------------------------------------
  Invariant 3 : the reachable set from the root equals marked plus
  what is reachable from the frontier.
-----------------------------------------------------------------*)
Inv3 ==
    ReachFrom({Root}) = marked \cup ReachFrom(frontier)

Invariants ==
    /\ Inv1
    /\ Inv2
    /\ Inv3

Properties == Invariants

Spec ==
    Init /\ [][Next]_vars

====