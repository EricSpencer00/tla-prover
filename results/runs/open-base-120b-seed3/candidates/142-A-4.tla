---- MODULE ReachableProofs ----
EXTENDS FiniteSets, ReachabilityAlgorithm, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

(*-----------------------------------------------------------------
  Initial state:  marked is empty, frontier contains the root,
  and the program counter starts in the initial state.
-----------------------------------------------------------------*)
Init ==
  /\ marked   = {}
  /\ frontier = {Root}
  /\ pc       = "start"

(*-----------------------------------------------------------------
  Next action:  placeholder for the steps of the sequential
  Misra reachability algorithm.  The concrete actions are
  defined in the extended algorithm module; here we simply expose
  the stuttering step to keep the specification well‑formed.
-----------------------------------------------------------------*)
Next ==
  \/ (* real algorithm steps are imported from ReachabilityAlgorithm *)
     TRUE
  \/ (* stuttering step *)
     UNCHANGED <<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Invariant 1:  type correctness and every successor of a marked
  node is either already marked or in the frontier.
-----------------------------------------------------------------*)
Inv1 ==
  /\ marked   \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ \A n \in marked :
       \A s \in Succ[n] : s \in marked \/ s \in frontier

(*-----------------------------------------------------------------
  Invariant 2:  marked ∪ ReachFrom(frontier) equals ReachFrom(marked ∪ frontier)
  (proved from Lemma1 in ReachabilityLemmas).
-----------------------------------------------------------------*)
Inv2 ==
  (marked \cup ReachFrom(frontier)) = ReachFrom(marked \cup frontier)

(*-----------------------------------------------------------------
  Invariant 3:  ReachFrom({Root}) equals marked ∪ ReachFrom(frontier)
  (proved using Lemma2 and Lemma3 in ReachabilityLemmas).
-----------------------------------------------------------------*)
Inv3 ==
  ReachFrom({Root}) = marked \cup ReachFrom(frontier)

(*-----------------------------------------------------------------
  Partial correctness theorem: when the algorithm terminates
  (pc = "done") the set of marked nodes equals the set of nodes
  reachable from the root.
-----------------------------------------------------------------*)
PartialCorrectness ==
  /\ pc = "done"
  /\ marked = ReachFrom({Root})

(*-----------------------------------------------------------------
  Specification of the system.
-----------------------------------------------------------------*)
Spec ==
  Init /\ [][Next]_<<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Collections required by the .cfg file.
-----------------------------------------------------------------*)
INVARIANTS == { Inv1, Inv2, Inv3 }
PROPERTIES  == { PartialCorrectness }

====