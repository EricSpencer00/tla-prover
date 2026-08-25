---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

(* ----------------------------------------------------------------------
   Concrete graph definition (will be substituted for Succ by the .cfg)
   ---------------------------------------------------------------------- *)
ConnectedToSomeButNotAll ==
  [n \in Nodes |-> 
    CASE n = 1 -> {2,3}
    [] n = 2 -> {3,4}
    [] n = 3 -> {1,4}
    [] n = 4 -> {1,2}
  ]

(* ----------------------------------------------------------------------
   Bounded sequence operator used in place of the infinite Seq
   ---------------------------------------------------------------------- *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "run"

(* ----------------------------------------------------------------------
   One step of the sequential reachability algorithm
   ---------------------------------------------------------------------- *)
Next ==
  \/ /\ pc = "run"
     /\ ∃ n \in frontier :
        /\ marked'   = marked \cup {n}
        /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
        /\ pc'       = "run"
  \/ /\ pc = "run"
     /\ frontier = {}
     /\ pc' = "done"
     /\ UNCHANGED <<marked, frontier>>

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* ----------------------------------------------------------------------
   Invariants
   ---------------------------------------------------------------------- *)
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ marked ∩ frontier = {}
  /\ pc \in {"run", "done"}

Inv1 ==
  ∀ n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
  frontier \subseteq Nodes \ marked

ReachableSet ==
  { n \in Nodes :
      ∃ s \in LimitedSeq(Nodes) :
        /\ Len(s) > 0
        /\ s[1] = Root
        /\ s[Len(s)] = n
        /\ \A i \in 1..Len(s)-1 : s[i+1] \in Succ[s[i]]
  }

Inv3 ==
  marked = ReachableSet

PartialCorrectness ==
  (frontier = {} /\ pc = "done") => marked = ReachableSet

(* ----------------------------------------------------------------------
   Liveness property
   ---------------------------------------------------------------------- *)
Termination == <> (frontier = {})

====