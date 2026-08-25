---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

(* Concrete graph with exactly 4 nodes, each having 2 successors *)
NodeSet == {"A", "B", "C", "D"}

ASSUME Nodes = NodeSet
ASSUME Root \in Nodes

ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> 
      CASE n = "A" -> {"B", "C"}
      [] n = "B" -> {"C", "D"}
      [] n = "C" -> {"D", "A"}
      [] n = "D" -> {"A", "B"}
      [] OTHER   -> {} ]

(* Compatibility: Succ is replaced by ConnectedToSomeButNotAll in the cfg *)
Succ == ConnectedToSomeButNotAll

(* Bounded sequence operator, overriding the infinite Seq *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

VARIABLES marked, frontier, pc

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "init"

Next ==
  \/ /\ frontier # {}
     /\ \E n \in frontier :
          /\ marked'   = marked \cup {n}
          /\ frontier' = (frontier \ {n}) \cup (ConnectedToSomeButNotAll[n] \ setdiff marked)
          /\ pc'       = pc
  \/ /\ frontier = {}
     /\ pc'       = "done"
     /\ UNCHANGED <<marked, frontier>>

Vars == <<marked, frontier, pc>>

Spec == Init /\ [][Next]_Vars

(* Reachable nodes defined via bounded sequences *)
Reachable ==
  { n \in Nodes :
      \E seq \in LimitedSeq(Nodes) :
        /\ Len(seq) >= 1
        /\ seq[1] = Root
        /\ seq[Len(seq)] = n
        /\ \A i \in 1..Len(seq)-1 :
             seq[i+1] \in ConnectedToSomeButNotAll[seq[i]]
  }

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "done"}

Inv1 == \A n \in marked :
          ConnectedToSomeButNotAll[n] \subseteq marked \cup frontier

Inv2 == marked = Reachable

Inv3 == \A n \in Nodes :
          (n \in marked) =>
            \E seq \in LimitedSeq(Nodes) :
              /\ Len(seq) >= 1
              /\ seq[1] = Root
              /\ seq[Len(seq)] = n
              /\ \A i \in 1..Len(seq)-1 :
                   seq[i+1] \in ConnectedToSomeButNotAll[seq[i]]

PartialCorrectness == (pc = "done") => (marked = Reachable)

Termination == <> (pc = "done")

====