---- MODULE Reachable ----
EXTENDS Sequences, Naturals

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

(* Helper definitions *)
SuccSet(S) == { x \in Nodes : ∃ n \in S : x \in Succ(n) }

RecSucc(S, 0) == S
RecSucc(S, k+1) == RecSucc(S, k) ∪ SuccSet(RecSucc(S, k))

ReachableFromSet(S) == { x \in Nodes : ∃ k \in Nat : x ∈ RecSucc(S, k) }

(* Initial state *)
Init == /\ marked = {}
      /\ frontier = {Root}
      /\ pc = "Start"

(* Main loop action *)
MainLoop == ∃ node \in frontier :
  ( (node \notin marked /\ marked' = marked ∪ {node} /\ frontier' = frontier ∪ SuccSet({node}) /\ pc' = "Start") \/
    (node \in marked /\ marked' = marked /\ frontier' = frontier \ {node} /\ pc' = "Start") )

(* Termination action *)
TermAction == /\ frontier = {}
            /\ pc' = "Done"
            /\ marked' = marked
            /\ frontier' = frontier

Next == MainLoop \/ TermAction

Spec == Init /\ [][Next]_{marked, frontier, pc}

TypeOK == marked ⊆ Nodes /\ frontier ⊆ Nodes

Inv1 == ∀ n ∈ marked : Succ(n) ⊆ marked ∪ frontier

Inv2 == marked ∪ ReachableFromSet(frontier) = ReachableFromSet(marked ∪ frontier)

Inv3 == ReachableFromSet({Root}) = marked ∪ ReachableFromSet(frontier)

PartialCorrectness == (pc = "Done" => marked = ReachableFromSet({Root}))

Termination == []<>( frontier = {} )

(* LimitedSeq alias *)
LimitedSeq == Seq

====