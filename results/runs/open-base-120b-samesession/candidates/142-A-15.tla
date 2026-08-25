---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Sequences

(*--------------------------------------------------------------------
  Constants required by the configuration
--------------------------------------------------------------------*)
CONSTANTS Nodes, Root, Succ

(*--------------------------------------------------------------------
  State variables of the sequential Misra reachability algorithm
--------------------------------------------------------------------*)
VARIABLES MARKED, FRONTIER, pc

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
\* The set of all nodes reachable from a set S using the successor
\* relation Succ (any number of steps, including zero).
Reach(S) ==
    { n \in Nodes :
        \E p \in Seq(Nodes) :
          /\ Len(p) > 0
          /\ p[1] \in S
          /\ \A i \in 1..(Len(p)-1) : p[i+1] \in Succ[p[i]]
          /\ n = p[Len(p)] }

(*--------------------------------------------------------------------
  Initial state (not specified in the description; a reasonable
  choice compatible with the invariants)
--------------------------------------------------------------------*)
Init ==
    /\ MARKED = {}
    /\ FRONTIER = {Root}
    /\ pc = "Init"
    /\ Root \in Nodes
    /\ \A n \in Nodes: Succ[n] \subseteq Nodes

(*--------------------------------------------------------------------
  Actions (place‑holders; the real algorithm is not detailed)
--------------------------------------------------------------------*)
InitStep ==
    /\ pc = "Init"
    /\ pc' = "Step"
    /\ UNCHANGED <<MARKED, FRONTIER>>

Step ==
    /\ pc = "Step"
    /\ (* a placeholder for the algorithm's main step;
          it leaves the variables unchanged in this skeleton *)
       UNCHANGED <<MARKED, FRONTIER>>
    /\ pc' = "Step"

Terminate ==
    /\ pc # "Done"
    /\ pc' = "Done"
    /\ UNCHANGED <<MARKED, FRONTIER>>

Next ==
    \/ InitStep
    \/ Step
    \/ Terminate

(*--------------------------------------------------------------------
  Invariants required for the proof
--------------------------------------------------------------------*)
\* Invariant 1: type correctness and every successor of a marked node
\* is either already marked or in the frontier.
Inv1 ==
    /\ MARKED \subseteq Nodes
    /\ FRONTIER \subseteq Nodes
    /\ pc \in {"Init", "Step", "Done"}
    /\ \A n \in MARKED : Succ[n] \subseteq (MARKED \cup FRONTIER)

\* Invariant 2: MARKED ∪ Reach(FRONTIER) = Reach(MARKED ∪ FRONTIER)
Inv2 ==
    MARKED \cup Reach(FRONTIER) = Reach(MARKED \cup FRONTIER)

\* Invariant 3: Reach({Root}) = MARKED ∪ Reach(FRONTIER)
Inv3 ==
    Reach({Root}) = MARKED \cup Reach(FRONTIER)

(*--------------------------------------------------------------------
  Collection of invariants for TLC
--------------------------------------------------------------------*)
INVARIANTS == { Inv1, Inv2, Inv3 }

(*--------------------------------------------------------------------
  Property expressing partial correctness (termination ⇒ correctness)
--------------------------------------------------------------------*)
PartialCorrectness ==
    [] (pc = "Done" => MARKED = Reach({Root}))

PROPERTIES == { PartialCorrectness }

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec ==
    Init /\ [][Next]_<<MARKED, FRONTIER, pc>>

====