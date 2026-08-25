---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

(* Override of the generic successor relation *)
ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> { (n % 4) + 1 , ((n + 1) % 4) + 1 } ]

(* Finite version of Seq for model checking *)
LimitedSeq == { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

VARIABLES marked, frontier, pc

Init ==
  /\ marked   = {}
  /\ frontier = {Root}
  /\ pc       = "run"

Next ==
  \/ /\ pc = "run"
     /\ \E n \in frontier :
          LET newMarked   == marked \cup {n}
              newFrontier == (frontier \ {n}) \cup (ConnectedToSomeButNotAll[n] \ newMarked)
          IN /\ marked'   = newMarked
             /\ frontier' = newFrontier
             /\ pc'       = IF newFrontier = {} THEN "done" ELSE "run"
  \/ /\ pc = "done"
     /\ UNCHANGED << marked, frontier, pc >>

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* ---------- Invariants ---------- *)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"run", "done"}

Inv1 ==
  \A n \in marked :
    ConnectedToSomeButNotAll[n] \subseteq marked \cup frontier

Inv2 ==
  marked \cap frontier = {}

Reachable ==
  { n \in Nodes :
      \E s \in LimitedSeq :
        /\ Len(s) >= 1
        /\ s[1] = Root
        /\ s[Len(s)] = n
        /\ \A i \in 1..(Len(s)-1) :
             s[i+1] \in ConnectedToSomeButNotAll[s[i]]
  }

Inv3 ==
  marked \cup frontier = Reachable

PartialCorrectness ==
  pc = "done" => marked = Reachable

(* ---------- Liveness property ---------- *)

Termination == <> (pc = "done")

====