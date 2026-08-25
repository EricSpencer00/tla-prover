---- MODULE ReachableProofs ----
EXTENDS Alg, GraphLemmas

CONSTANTS Nodes, Root

VARIABLES Marked, Frontier, pc

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ Marked = {}
    /\ Frontier = {Root}
    /\ pc = "init"

(*-----------------------------------------------------------------
  Next-state relation (abstract)
-----------------------------------------------------------------*)
Next ==
    \/ /\ pc = "init"
       /\ pc' = "run"
       /\ UNCHANGED <<Marked, Frontier>>
    \/ /\ pc = "run"
       /\ pc' = "run"
       /\ UNCHANGED <<Marked, Frontier>>
    \/ /\ pc = "run"
       /\ Frontier = {}
       /\ pc' = "done"
       /\ UNCHANGED <<Marked, Frontier>>
    \/ UNCHANGED <<Marked, Frontier, pc>>

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
Invariant1 ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ \A n \in Marked :
          \A s \in Succ[n] :
              s \in Marked \/ s \in Frontier

Invariant2 ==
    (Marked \cup ReachableFrom(Frontier)) = ReachableFrom(Marked \cup Frontier)

Invariant3 ==
    ReachableFrom({Root}) = Marked \cup ReachableFrom(Frontier)

(*-----------------------------------------------------------------
  Property expressing partial correctness upon termination
-----------------------------------------------------------------*)
TerminationCorrectness ==
    (pc = "done") => (Marked = ReachableFrom({Root}))

(*-----------------------------------------------------------------
  Collections required by the configuration file
-----------------------------------------------------------------*)
INVARIANTS == <<Invariant1, Invariant2, Invariant3>>
PROPERTIES == <<TerminationCorrectness>>

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

====