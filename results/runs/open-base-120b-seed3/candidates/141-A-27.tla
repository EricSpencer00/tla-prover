---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

(*--- Helper definitions ---------------------------------------------------*)
Edge == { <<n, m>> : n \in Nodes /\ m \in Succ[n] }

Reach(S) ==
  LET R == Edge IN
    S \cup { y \in Nodes : \E x \in S : <<x, y>> \in TC(R) }

(*--- Operators required by the .cfg ---------------------------------------*)
ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq(S) == { s \in Seq(S) : Len(s) <= 5 }

(*--- State definition -----------------------------------------------------*)
Init ==
  /\ marked  = {}
  /\ frontier = {Root}
  /\ pc      = "run"

vars == <<marked, frontier, pc>>

(*--- Transition relation ---------------------------------------------------*)
ChooseAndProcess ==
  /\ frontier # {}
  /\ \E n \in frontier :
       ( ( /\ n \notin marked
            /\ marked'   = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
            /\ UNCHANGED pc )
       \/ ( /\ n \in marked
            /\ marked'   = marked
            /\ frontier' = frontier \ {n}
            /\ UNCHANGED pc ) )

Terminate ==
  /\ frontier = {}
  /\ pc = "run"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

StutterDone ==
  /\ pc = "done"
  /\ UNCHANGED <<marked, frontier, pc>>

Next == ChooseAndProcess \/ Terminate \/ StutterDone

(*--- Specification --------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*--- Invariants -----------------------------------------------------------*)
TypeOK ==
  /\ marked  \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"run", "done"}

Inv1 ==
  \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
  marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 ==
  Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
  /\ pc = "done"
  => marked = Reach({Root})

(*--- Liveness property ----------------------------------------------------*)
Termination == <> (pc = "done")

====