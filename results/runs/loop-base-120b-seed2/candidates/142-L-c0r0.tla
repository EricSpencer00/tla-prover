---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, SeqReachAlg, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES Marked, Frontier, pc

(*-----------------------------------------------------------------
  Type correctness and basic definitions
-----------------------------------------------------------------*)
TypeInvariant ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ pc \in {"start", "loop", "done"}

(*-----------------------------------------------------------------
  Invariant 1: type correctness plus successor property
-----------------------------------------------------------------*)
Inv1 ==
    /\ TypeInvariant
    /\ \A n \in Marked :
          \A s \in Succ[n] : s \in Marked \/ Frontier

(*-----------------------------------------------------------------
  Invariant 2: relationship between marked, frontier and reachability
-----------------------------------------------------------------*)
Inv2 ==
    Marked \cup Reachable(Frontier) = Reachable(Marked \cup Frontier)

(*-----------------------------------------------------------------
  Invariant 3: reachable from the root equals marked plus reachable frontier
-----------------------------------------------------------------*)
Inv3 ==
    Reachable({Root}) = Marked \cup Reachable(Frontier)

(*-----------------------------------------------------------------
  Collection of all invariants required by the proof
-----------------------------------------------------------------*)
INVARIANTS == Inv1 /\ Inv2 /\ Inv3

(*-----------------------------------------------------------------
  Initial state (as in the sequential algorithm)
-----------------------------------------------------------------*)
INIT ==
    /\ Marked = {}
    /\ Frontier = {Root}
    /\ pc = "start"

(*-----------------------------------------------------------------
  Algorithm actions (abstracted)
-----------------------------------------------------------------*)
AddSuccessor ==
    /\ pc = "loop"
    /\ \E n \in Marked :
          \E s \in Succ[n] :
              /\ s \notin Marked
              /\ Marked' = Marked \cup {s}
              /\ Frontier' = Frontier
              /\ pc' = "loop"

AdvanceFrontier ==
    /\ pc = "loop"
    /\ Frontier # {}
    /\ \E f \in Frontier :
          /\ Marked' = Marked
          /\ Frontier' = Frontier \ {f}
          /\ pc' = "loop"

Terminate ==
    /\ pc = "loop"
    /\ Frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<Marked, Frontier>>

NEXT == AddSuccessor \/ AdvanceFrontier \/ Terminate

(*-----------------------------------------------------------------
  Specification of the system
-----------------------------------------------------------------*)
Spec == INIT /\ [][NEXT]_<<Marked, Frontier, pc>> /\ INVARIANTS

(*-----------------------------------------------------------------
  Safety properties (the invariants)
-----------------------------------------------------------------*)
PROPERTIES == INVARIANTS

====