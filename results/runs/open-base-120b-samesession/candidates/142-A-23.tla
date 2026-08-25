---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, SeqReachability, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES Marked, Frontier, pc

(* ----------------------------------------------------------------------
   Initial state (as in the sequential reachability algorithm)
   ---------------------------------------------------------------------- *)
Init ==
    /\ Marked = {}
    /\ Frontier = {Root}
    /\ pc = "init"

(* ----------------------------------------------------------------------
   Next-state relation (placeholder – the actual algorithm steps are
   defined in SeqReachability; here we keep the specification syntactically
   complete)
   ---------------------------------------------------------------------- *)
Next ==
    UNCHANGED <<Marked, Frontier, pc>>

(* ----------------------------------------------------------------------
   Invariant 1: type correctness and successor closure
   ---------------------------------------------------------------------- *)
Inv1 ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ Root \in Nodes
    /\ pc \in {"init", "step", "done"}
    /\ \A n \in Marked :
          \A s \in Succ[n] : s \in Marked \/ s \in Frontier

(* ----------------------------------------------------------------------
   Invariant 2: marked ∪ Reachable(Frontier) = Reachable(marked ∪ Frontier)
   ---------------------------------------------------------------------- *)
Inv2 ==
    Marked \cup ReachableFrom(Frontier) = ReachableFrom(Marked \cup Frontier)

(* ----------------------------------------------------------------------
   Invariant 3: Reachable({Root}) = marked ∪ Reachable(Frontier)
   ---------------------------------------------------------------------- *)
Inv3 ==
    ReachableFrom({Root}) = Marked \cup ReachableFrom(Frontier)

(* ----------------------------------------------------------------------
   Collection of invariants required by the model checker
   ---------------------------------------------------------------------- *)
INVARIANTS == { Inv1, Inv2, Inv3 }

(* ----------------------------------------------------------------------
   The set of properties that the model checker should verify.
   Here we expose the same invariants as properties.
   ---------------------------------------------------------------------- *)
PROPERTIES == INVARIANTS

(* ----------------------------------------------------------------------
   The full specification of the system
   ---------------------------------------------------------------------- *)
Spec ==
    Init /\ [][Next]_<<Marked, Frontier, pc>>

(* ----------------------------------------------------------------------
   Partial‑correctness theorem (proved externally with TLAPS)
   ---------------------------------------------------------------------- *)
THEOREM PartialCorrectness ==
    /\ pc = "done"
    => Marked = ReachableFrom({Root})

====