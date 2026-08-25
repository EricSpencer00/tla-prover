---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ, n1, n2, n3, n4

(* concrete graph definition – each node has exactly two successors *)
ASSUME Nodes = {n1, n2, n3, n4}
ASSUME Root \in Nodes
ASSUME Root = n1

ConnectedToSomeButNotAll == 
  [i \in Nodes |-> 
    CASE i = n1 -> {n2, n3}
         [] i = n2 -> {n3, n4}
         [] i = n3 -> {n4, n1}
         [] i = n4 -> {n1, n2}
  ]

(* bounded sequence operator used instead of the infinite Seq *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

VARIABLES marked, frontier, pc

(* initial state *)
Init == 
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "init"

(* one step of the sequential Misra reachability algorithm *)
Next == 
  \/ /\ pc = "done"
     /\ UNCHANGED <<marked, frontier, pc>>
  \/ /\ pc # "done"
     /\ frontier # {}
     /\ \E n \in frontier:
          /\ marked' = marked \cup {n}
          /\ frontier' = (frontier \ {n}) \cup ConnectedToSomeButNotAll[n]
          /\ pc' = IF frontier' = {} THEN "done" ELSE "run"
  \/ /\ pc # "done"
     /\ frontier = {}
     /\ pc' = "done"
     /\ UNCHANGED <<marked, frontier>>

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* type correctness invariant *)
TypeOK == 
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "run", "done"}

(* invariant 1 – successor closure (trivial because of graph definition) *)
Inv1 == 
  \A n \in marked: ConnectedToSomeButNotAll[n] \subseteq Nodes

(* invariant 2 – frontier is always a subset of Nodes *)
Inv2 == frontier \subseteq Nodes

(* reachable set defined using bounded sequences *)
ReachableSet == 
  { y \in Nodes :
      \E s \in LimitedSeq(Nodes) :
        /\ Len(s) >= 1
        /\ s[1] = Root
        /\ s[Len(s)] = y
        /\ \A i \in 1..Len(s)-1 : s[i+1] \in ConnectedToSomeButNotAll[s[i]]
  }

(* invariant 3 – when the algorithm finishes, the marked set equals the reachable set *)
Inv3 == (pc = "done") => marked = ReachableSet

(* partial correctness property – same as Inv3, kept as a separate name for the cfg *)
PartialCorrectness == Inv3

(* termination property – eventually the algorithm reaches the completed state *)
Termination == <> (pc = "done")

====