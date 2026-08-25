---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

(* Concrete definitions for the constants to obtain a finite model. *)
ASSUME Nodes = {1, 2, 3, 4}
ASSUME Root \in Nodes

(* Operator that will replace Succ in the configuration. *)
ConnectedToSomeButNotAll ==
  [n \in Nodes |-> 
    CASE n = 1 -> {2, 3}
    [] n = 2 -> {3, 4}
    [] n = 3 -> {1, 4}
    [] n = 4 -> {1, 2}
  ]

(* Limited version of Seq used for bounded paths. *)
LimitedSeq == { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

VARIABLES Marked, Frontier, pc

(* Reachable nodes via bounded sequences (using Succ, which will be
   substituted by ConnectedToSomeButNotAll). *)
Reachable ==
  { n \in Nodes :
      \E s \in LimitedSeq :
        /\ Len(s) > 0
        /\ s[1] = Root
        /\ s[Len(s)] = n
        /\ \A i \in 1..Len(s)-1 : s[i+1] \in Succ[s[i]]
  }

Init ==
  /\ pc = "init"
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ UNCHANGED <<>>

InitStep ==
  /\ pc = "init"
  /\ Marked' = {Root}
  /\ Frontier' = Succ[Root] \ {Root}
  /\ pc' = "step"
  /\ UNCHANGED <<>>

Step ==
  /\ pc = "step"
  /\ Frontier # {}
  /\ \E n \in Frontier :
        /\ Marked' = Marked \cup {n}
        /\ Frontier' = (Frontier \ {n}) \cup (Succ[n] \ Marked')
        /\ UNCHANGED pc

Done ==
  /\ pc = "done"
  /\ UNCHANGED <<Marked, Frontier, pc>>

Next == InitStep \/ Step \/ Done

Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

(* Type correctness invariant *)
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"init", "step", "done"}

(* Invariant 1: successor closure *)
Inv1 == \A n \in Marked : Succ[n] \subseteq Marked \cup Frontier

(* Invariant 2: Marked equals the set of reachable nodes *)
Inv2 == Marked = Reachable

(* Invariant 3: Frontier is exactly the reachable nodes not yet marked *)
Inv3 == Frontier = Reachable \ Marked

(* Partial correctness: when the algorithm finishes, all reachable nodes are marked *)
PartialCorrectness == (pc = "done") => (Marked = Reachable)

(* Liveness property: eventual termination *)
Termination == <> (pc = "done")

====