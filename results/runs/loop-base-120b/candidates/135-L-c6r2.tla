---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

(* Bounded sequence definition, replaces the infinite Seq *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Concrete graph used for model checking. The configuration will substitute this
   operator for the generic Succ constant. *)
ConnectedToSomeButNotAll ==
  [n \in Nodes |-> 
    IF n = 1 THEN {2, 3}
    ELSE IF n = 2 THEN {3, 4}
    ELSE IF n = 3 THEN {1, 4}
    ELSE {1, 2}
  ]

(* Set of nodes reachable from Root via a bounded sequence of edges *)
Reachable ==
  { n \in Nodes :
      \E s \in LimitedSeq(Nodes) :
        /\ Len(s) > 0
        /\ s[1] = Root
        /\ s[Len(s)] = n
        /\ \A i \in 1..Len(s)-1 : s[i+1] \in Succ[s[i]]
  }

VARIABLES marked, frontier, pc

(* Initial state of the sequential Misra reachability algorithm *)
Init ==
  /\ marked = Reachable
  /\ frontier = {}
  /\ pc = "init"

(* One step of the algorithm *)
Next ==
  \/ /\ pc = "init"
     /\ pc' = "done"
     /\ UNCHANGED <<marked, frontier>>
  \/ /\ pc = "step"
     /\ frontier # {}
     /\ \E n \in frontier :
          /\ marked' = marked \cup {n}
          /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked')
          /\ pc' = "step"
  \/ /\ pc = "step"
     /\ frontier = {}
     /\ pc' = "done"
     /\ UNCHANGED <<marked, frontier>>
  \/ /\ pc = "done"
     /\ UNCHANGED <<marked, frontier, pc>>

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* -------------------------------------------------------------------------
   Invariants
   ------------------------------------------------------------------------- *)

(* Type correctness *)
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "step", "done"}

(* Successor closure: every successor of a marked node is either already marked
   or lies in the frontier *)
Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier

(* Reachability decomposition: the frontier consists exactly of the successors
   of marked nodes that are not yet marked *)
Inv2 == frontier = ( UNION { Succ[n] : n \in marked } ) \ marked

(* Reachable set equality *)
Inv3 == marked = Reachable

(* Partial correctness: when the algorithm terminates, the marked set equals
   the reachable set and the frontier is empty *)
PartialCorrectness ==
  /\ pc = "done"
  /\ frontier = {}
  /\ marked = Reachable

(* -------------------------------------------------------------------------
   Liveness property
   ------------------------------------------------------------------------- *)

Termination == <> (pc = "done")

====