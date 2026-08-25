---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

(*--------------------------------------------------------------------
  Concrete graph definition (overridden by the .cfg)
--------------------------------------------------------------------*)
ConnectedToSomeButNotAll ==
  [n \in Nodes |-> CHOOSE S \in SUBSET Nodes : Cardinality(S) = 2]

(* The .cfg substitutes ConnectedToSomeButNotAll for Succ,
   therefore all occurrences of Succ below will be replaced. *)

(*--------------------------------------------------------------------
  Helper: a finite version of Seq (bounded by the number of nodes)
--------------------------------------------------------------------*)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(*--------------------------------------------------------------------
  Reachable set defined via bounded sequences
--------------------------------------------------------------------*)
Reachable ==
  { n \in Nodes :
      \E seq \in LimitedSeq(Nodes) :
        /\ Len(seq) >= 1
        /\ seq[1] = Root
        /\ seq[Len(seq)] = n
        /\ \A i \in 1..Len(seq)-1 :
            seq[i+1] \in Succ[seq[i]]
  }

(*--------------------------------------------------------------------
  Initialization and transition relation
--------------------------------------------------------------------*)
Init ==
  /\ pc = "init"
  /\ marked = {}
  /\ frontier = {Root}
  /\ TypeOK

Next ==
  \/ /\ pc = "init"
        /\ pc' = "step"
        /\ UNCHANGED <<marked, frontier>>
  \/ /\ pc = "step"
        /\ frontier # {}
        /\ let newFrontier ==
               { s \in UNION { Succ[n] : n \in frontier } \ (marked \cup frontier) }
           in
           /\ marked' = marked \cup frontier
           /\ frontier' = newFrontier
           /\ pc' = IF newFrontier = {} THEN "done" ELSE "step"
  \/ /\ pc = "done"
        /\ UNCHANGED <<marked, frontier, pc>>

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*--------------------------------------------------------------------
  Type correctness invariant
--------------------------------------------------------------------*)
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "step", "done"}

(*--------------------------------------------------------------------
  Algorithm invariants
--------------------------------------------------------------------*)
Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 == /\ marked \cap frontier = {}
        /\ frontier \subseteq Nodes \ marked

Inv3 == marked \cup frontier = Reachable

PartialCorrectness ==
  /\ pc = "done"
  => marked = Reachable

(*--------------------------------------------------------------------
  Liveness property (termination)
--------------------------------------------------------------------*)
Termination == <> (pc = "done")

=============================================================================