---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

(* Concrete definitions for the constants *)
Nodes == {"n1", "n2", "n3", "n4"}
Root  == "n1"

(* Operator that will replace Succ in the configuration *)
ConnectedToSomeButNotAll ==
  [n \in Nodes |-> 
    CASE n = "n1" -> {"n2", "n3"}
    [] n = "n2" -> {"n3", "n4"}
    [] n = "n3" -> {"n1", "n4"}
    [] n = "n4" -> {"n1", "n2"}]

(* The constant Succ is defined as the operator above so the .cfg substitution works *)
Succ == ConnectedToSomeButNotAll

(* Bounded version of Seq *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

VARIABLES marked, frontier, pc

(* Initial state *)
Init ==
  /\ marked  = {}
  /\ frontier = {Root}
  /\ pc = "start"

(* One step of the sequential reachability algorithm *)
Next ==
  \/ /\ pc = "start"
     /\ frontier # {}
     /\ LET n == CHOOSE x \in frontier
        IN /\ marked'   = marked \cup {n}
           /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
           /\ pc'       = "start"
  \/ /\ pc = "start"
     /\ frontier = {}
     /\ pc' = "done"
     /\ UNCHANGED <<marked, frontier>>

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* Type correctness invariant *)
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"start", "done"}

(* Invariant 1: successor closure *)
Inv1 ==
  \A n \in marked : Succ[n] \subseteq marked \cup frontier

(* Invariant 2: root is always discovered or processed *)
Inv2 ==
  Root \in marked \cup frontier

(* Reachability definition using the bounded sequence operator *)
Reachable(n) ==
  \E s \in LimitedSeq(Nodes) :
    /\ Len(s) >= 1
    /\ s[1] = Root
    /\ s[Len(s)] = n
    /\ \A i \in 1..Len(s)-1 : s[i+1] \in Succ[s[i]]

(* Invariant 3: marked set equals the set of reachable nodes *)
Inv3 ==
  \A n \in Nodes : (n \in marked) <=> Reachable(n)

(* Partial correctness: when the algorithm terminates, the marked set is exactly the reachable set *)
PartialCorrectness ==
  (pc = "done") => \A n \in Nodes : (n \in marked) <=> Reachable(n)

(* Liveness property: the algorithm eventually reaches the done state *)
Termination == <> (pc = "done")

====