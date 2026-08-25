---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Successor operator that will replace Succ after the .cfg substitution
-----------------------------------------------------------------*)
ConnectedToSomeButNotAll(n) == { m \in Nodes : m # n }

(*-----------------------------------------------------------------
  Finite version of Seq required by the .cfg substitution
-----------------------------------------------------------------*)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= 5 }

(*-----------------------------------------------------------------
  Reachability operator (least fixed point of the successor relation)
-----------------------------------------------------------------*)
RECURSIVE Reach(_)
Reach(S) ==
  IF S = {} THEN {}
  ELSE
    LET Y == S \cup UNION { Succ[n] : n \in S } IN
      IF Y = S THEN S ELSE Reach(Y)

ReachFromRoot == Reach({Root})

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "run"

(*-----------------------------------------------------------------
  Main step (choose a node from the frontier)
-----------------------------------------------------------------*)
Step ==
  /\ pc = "run"
  /\ frontier # {}
  /\ \E n \in frontier :
        ( /\ n \notin marked
           /\ marked'   = marked \cup {n}
           /\ frontier' = frontier \cup Succ[n]
           /\ pc'       = pc
        )
     \/ ( /\ n \in marked
           /\ marked'   = marked
           /\ frontier' = frontier \ {n}
           /\ pc'       = pc
        )

(*-----------------------------------------------------------------
  Termination transition
-----------------------------------------------------------------*)
Terminate ==
  /\ pc = "run"
  /\ frontier = {}
  /\ pc'       = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  Step \/ Terminate

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"run", "done"}

Inv1 ==
  \A m \in marked : Succ[m] \subseteq marked \cup frontier

Inv2 ==
  (marked \cup Reach(frontier)) = Reach(marked \cup frontier)

Inv3 ==
  ReachFromRoot = marked \cup Reach(frontier)

PartialCorrectness ==
  (pc = "done") => marked = ReachFromRoot

(*-----------------------------------------------------------------
  Liveness property
-----------------------------------------------------------------*)
Termination == <> (pc = "done")

====