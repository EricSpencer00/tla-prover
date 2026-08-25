---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

(* Concrete values for the constants *)
ASSUME Nodes = {1, 2, 3, 4}
ASSUME Root = 1

(* Operator that will be substituted for Succ in the .cfg *)
ConnectedToSomeButNotAll(n) ==
  CASE n = 1 -> {2, 3}
  []  n = 2 -> {3, 4}
  []  n = 3 -> {4, 1}
  []  n = 4 -> {1, 2}
  []  OTHER -> {}

(* Bounded sequence operator that replaces Seq *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

VARIABLES Marked, Frontier, pc

Vars == <<Marked, Frontier, pc>>

(* Initial state *)
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "running"

(* Main step of the sequential reachability algorithm *)
Process ==
  /\ \E n \in Frontier :
        /\ Marked'   = Marked \cup {n}
        /\ Frontier' = (Frontier \ {n}) \cup (ConnectedToSomeButNotAll(n) \ Marked)
        /\ pc'       = pc

(* Termination step *)
Done ==
  /\ Frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<Marked, Frontier>>

Next == \/ Process \/ Done

(* Overall specification *)
Spec == Init /\ [][Next]_Vars

(* Reachable nodes defined via bounded paths *)
ReachableSet ==
  { n \in Nodes :
        \E s \in LimitedSeq(Nodes) :
          /\ Len(s) >= 1
          /\ s[1] = Root
          /\ s[Len(s)] = n
          /\ \A i \in 1..(Len(s) - 1) :
                s[i+1] \in ConnectedToSomeButNotAll(s[i])
  }

(* Invariants required by the .cfg *)

TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Inv1 ==
  \A n \in Marked :
        ConnectedToSomeButNotAll(n) \subseteq Marked \cup Frontier

Inv2 ==
  /\ Marked \cap Frontier = {}
  /\ \A n \in Nodes : (n \in Marked) \/ (n \in Frontier) \/ (n \notin Marked \cup Frontier)

Inv3 ==
  Marked \subseteq ReachableSet

PartialCorrectness ==
  (pc = "done") => (Marked = ReachableSet)

(* Liveness property *)
Termination == <> (pc = "done")
====