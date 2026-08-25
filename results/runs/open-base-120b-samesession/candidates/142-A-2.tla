---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Sequences, SeqReachability, ReachabilityLemmas

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Initial state: start with only the root in the frontier,
  nothing marked yet, and the algorithm ready to run.
-----------------------------------------------------------------*)
Init ==
    /\ marked   = {}
    /\ frontier = {Root}
    /\ pc       = "run"
    /\ marked   \subseteq Nodes
    /\ frontier \subseteq Nodes

(*-----------------------------------------------------------------
  Transition relation: pick a node from the frontier, mark it,
  add its successors to the frontier, and possibly terminate.
-----------------------------------------------------------------*)
Next ==
    \/ /\ pc = "run"
       /\ \E n \in frontier:
            LET succs == Succ[n] IN
            /\ marked'   = marked \cup {n}
            /\ frontier' = (frontier \ {n}) \cup succs
            /\ pc'       = IF frontier' = {} THEN "halt" ELSE "run"
    \/ /\ pc = "halt"
       /\ UNCHANGED <<marked, frontier, pc>>

Spec == Init /\ [][Next]_vars

(*-----------------------------------------------------------------
  Invariant 1: type correctness and successor condition.
-----------------------------------------------------------------*)
Inv1 ==
    /\ marked   \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "halt"}
    /\ \A n \in marked: Succ[n] \subseteq marked \cup frontier

(*-----------------------------------------------------------------
  Invariant 2: marked ∪ ReachableFrom(frontier) = ReachableFrom(marked ∪ frontier)
-----------------------------------------------------------------*)
Inv2 ==
    marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

(*-----------------------------------------------------------------
  Invariant 3: ReachableFrom({Root}) = marked ∪ ReachableFrom(frontier)
-----------------------------------------------------------------*)
Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

INVARIANTS == {Inv1, Inv2, Inv3}

(*-----------------------------------------------------------------
  Partial correctness: when the algorithm halts, the marked set equals
  the set of nodes reachable from the root.
-----------------------------------------------------------------*)
FinalCorrectness ==
    [] (pc = "halt" => marked = ReachableFrom({Root}))

PROPERTIES == {FinalCorrectness}
====