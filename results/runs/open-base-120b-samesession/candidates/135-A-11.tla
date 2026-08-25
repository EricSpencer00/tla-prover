---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

(*-----------------------------------------------------------------
   Initialization
-----------------------------------------------------------------*)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "run"

(*-----------------------------------------------------------------
   Next-state relation
-----------------------------------------------------------------*)
Next ==
  \/ /\ pc = "run"
     /\ ∃ n \in frontier :
          /\ marked' = marked \cup {n}
          /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
          /\ pc' = IF frontier' = {} THEN "done" ELSE "run"
  \/ /\ pc = "done"
     /\ UNCHANGED <<marked, frontier, pc>>

(*-----------------------------------------------------------------
   Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*-----------------------------------------------------------------
   Bounded version of Seq (used for path quantification)
-----------------------------------------------------------------*)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(*-----------------------------------------------------------------
   Concrete successor relation used for model checking
-----------------------------------------------------------------*)
ConnectedToSomeButNotAll ==
  [n \in Nodes |-> 
    CHOOSE S \in SUBSET Nodes :
      /\ Cardinality(S) = 2
      /\ n \notin S]

(*-----------------------------------------------------------------
   Reachability definitions
-----------------------------------------------------------------*)
Paths ==
  { p \in LimitedSeq(Nodes) :
      /\ Len(p) >= 1
      /\ p[1] = Root
      /\ \A i \in 1 .. Len(p)-1 : p[i+1] \in Succ[p[i]] }

ReachableSet ==
  { n \in Nodes : \E p \in Paths : p[Len(p)] = n }

(*-----------------------------------------------------------------
   Type correctness invariant
-----------------------------------------------------------------*)
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"run", "done"}

(*-----------------------------------------------------------------
   Algorithm invariants
-----------------------------------------------------------------*)
Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 == /\ frontier \cap marked = {}
        /\ frontier \subseteq Nodes

Inv3 == marked = ReachableSet

PartialCorrectness == (pc = "done") => (marked = Nodes)

(*-----------------------------------------------------------------
   Liveness property
-----------------------------------------------------------------*)
Termination == <> (pc = "done")

====