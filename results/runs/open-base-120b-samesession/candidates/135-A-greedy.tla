---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

(*-----------------------------------------------------------------
  Concrete graph: each node has exactly two successors.
  The cfg will replace uses of Succ with ConnectedToSomeButNotAll.
-----------------------------------------------------------------*)
ConnectedToSomeButNotAll(n) ==
  CASE n = "n1" -> {"n2","n3"}
  [] n = "n2" -> {"n3","n4"}
  [] n = "n3" -> {"n1","n4"}
  [] n = "n4" -> {"n1","n2"}
  [] OTHER   -> {}

(*-----------------------------------------------------------------
  Bounded sequence operator used in reachability definition.
-----------------------------------------------------------------*)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

VARIABLES Marked, Frontier, pc

vars == <<Marked, Frontier, pc>>

(*-----------------------------------------------------------------
  Initial state.
-----------------------------------------------------------------*)
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "init"

(*-----------------------------------------------------------------
  One step of the algorithm.
-----------------------------------------------------------------*)
Step ==
  /\ pc \in {"init","step"}
  /\ Frontier # {}
  /\ \E n \in Frontier:
        /\ NewMarked   = Marked \cup Succ[n]
        /\ NewFrontier = (Frontier \ {n}) \cup (Succ[n] \ Marked)
        /\ Marked'    = NewMarked
        /\ Frontier'  = NewFrontier
        /\ pc'        = "step"

(*-----------------------------------------------------------------
  Termination action.
-----------------------------------------------------------------*)
Done ==
  /\ pc # "done"
  /\ Frontier = {}
  /\ Marked'   = Marked
  /\ Frontier' = Frontier
  /\ pc'       = "done"

Next == Step \/ Done

Spec == Init /\ [][Next]_vars

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"init","step","done"}

Inv1 == \A n \in Marked : Succ[n] \subseteq Marked

Inv2 == Marked = {Root} \cup (UNION { Succ[n] : n \in Marked })

Reachable(root) ==
  { n \in Nodes :
      \E s \in LimitedSeq(Nodes) :
        /\ Len(s) > 0
        /\ s[1] = root
        /\ s[Len(s)] = n
        /\ \A i \in 1..Len(s)-1 : s[i+1] \in Succ[s[i]]
  }

Inv3 == Marked = Reachable(Root)

PartialCorrectness ==
  (pc = "done") => (Frontier = {} /\ Marked = Reachable(Root))

(*-----------------------------------------------------------------
  Liveness property
-----------------------------------------------------------------*)
Termination == <> (pc = "done")

====