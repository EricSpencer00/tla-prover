---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

(* Concrete graph for the configuration *)
ASSUME Nodes = {1, 2, 3, 4}
ASSUME Root \in Nodes

(* Bounded successor relation: each node has exactly two successors *)
ConnectedToSomeButNotAll(n) ==
  CASE n = 1 -> {2, 3}
  [] n = 2 -> {3, 4}
  [] n = 3 -> {1, 4}
  [] n = 4 -> {1, 2}
  [] OTHER  -> {}

(* LimitedSeq: finite sequences bounded by the number of nodes *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

VARIABLES Marked, Frontier, pc

(* Initial state *)
Init ==
  /\ Marked = {Root}
  /\ Frontier = {Root}
  /\ pc = "Init"

(* Transition relation *)
Next ==
  \/ /\ pc = "Init"
     /\ pc' = "Run"
     /\ UNCHANGED <<Marked, Frontier>>
  \/ /\ pc = "Run"
     /\ \E n \in Frontier :
          LET newSucc == Succ[n] \ Marked IN
          /\ Marked' = Marked \cup newSucc
          /\ Frontier' = (Frontier \ {n}) \cup newSucc
          /\ pc' = IF Frontier' = {} THEN "Done" ELSE "Run"
  \/ /\ pc = "Done"
     /\ UNCHANGED <<Marked, Frontier, pc>>

(* Overall specification *)
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

(* Invariant: type correctness *)
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"Init", "Run", "Done"}

(* Invariant 1: successor closure for marked nodes *)
Inv1 ==
  \A n \in Marked : Succ[n] \subseteq Marked \cup Frontier

(* Invariant 2: frontier consists of marked nodes with unmarked successors *)
Inv2 ==
  Frontier = { n \in Marked : \E m \in Succ[n] : m \notin Marked }

(* Reachable nodes defined via bounded sequences *)
Reachable ==
  { v \in Nodes :
      \E s \in LimitedSeq(Nodes) :
        /\ Len(s) > 0
        /\ s[1] = Root
        /\ s[Len(s)] = v
        /\ \A i \in 1..Len(s)-1 : s[i+1] \in Succ[s[i]]
  }

(* Invariant 3: Marked is a subset of the reachable set *)
Inv3 == Marked \subseteq Reachable

(* Partial correctness: when the algorithm finishes, Marked equals Reachable *)
PartialCorrectness == (Frontier = {} ) => (Marked = Reachable)

(* Liveness property: termination *)
Termination == <> (Frontier = {})

====