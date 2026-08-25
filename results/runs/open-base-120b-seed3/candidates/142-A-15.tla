---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences

(*--------------------------------------------------------------------
  Constants required by the configuration
---------------------------------------------------------------------*)
CONSTANTS Nodes, Root

(*--------------------------------------------------------------------
  Import the sequential reachability algorithm and the graph‑theoretic
  lemmas needed for the proof.
---------------------------------------------------------------------*)
INSTANCE SeqReach AS Alg
INSTANCE ReachabilityProofs AS L

(*--------------------------------------------------------------------
  State variables (the algorithm already declares these, we re‑declare
  them here to make the spec self‑contained)
---------------------------------------------------------------------*)
VARIABLES Marked, Frontier, pc
vars == <<Marked, Frontier, pc>>

(*--------------------------------------------------------------------
  Initialization and next‑state relation are taken directly from the
  algorithm module.
---------------------------------------------------------------------*)
Init == Alg!Init
Next == Alg!Next

(*--------------------------------------------------------------------
  The overall specification
---------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*--------------------------------------------------------------------
  Invariant 1 : type correctness and successor condition
---------------------------------------------------------------------*)
Inv1 == 
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ \A n \in Marked :
        \A s \in Alg!Succ[n] :
            s \in Marked \/ Frontier

(*--------------------------------------------------------------------
  Invariant 2 : relationship between marked/frontier and reachability
---------------------------------------------------------------------*)
Inv2 == 
  (Marked \cup L!ReachableFrom(Frontier)) = L!ReachableFrom(Marked \cup Frontier)

(*--------------------------------------------------------------------
  Invariant 3 : marked set together with reachable from frontier equals
                the reachable set from the root
---------------------------------------------------------------------*)
Inv3 == 
  L!ReachableFrom({Root}) = Marked \cup L!ReachableFrom(Frontier)

(*--------------------------------------------------------------------
  Collection of invariants for TLC
---------------------------------------------------------------------*)
INVARIANTS == {Inv1, Inv2, Inv3}

(*--------------------------------------------------------------------
  Partial correctness theorem (expressed as a state property for TLC)
---------------------------------------------------------------------*)
PartialCorrectness == 
  (¬Enabled Next) => (Marked = L!ReachableFrom({Root}))

(*--------------------------------------------------------------------
  Additional properties for TLC
---------------------------------------------------------------------*)
PROPERTIES == {PartialCorrectness}
=============================================================================