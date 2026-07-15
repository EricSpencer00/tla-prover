---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*--------------------------------------------------------------------
  Constants required by the .cfg
--------------------------------------------------------------------*)
CONSTANTS Nodes, Root, Succ, Seq

(*--------------------------------------------------------------------
  Derived sets and helper definitions
--------------------------------------------------------------------*)
Node == Nodes
SeqBound == Cardinality(Nodes) \* maximum length of a path

Seq == [i \in 0..SeqBound |-> Node] \* sequences of nodes, length bounded

(*--------------------------------------------------------------------
  State variables inherited from the algorithm specification
--------------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*--------------------------------------------------------------------
  Safety predicate (type correctness)
--------------------------------------------------------------------*)
TypeOK == 
  /\ marked \in SUBSET Node
  /\ frontier \in SUBSET Node
  /\ pc \in {"Init", "Step", "Done"}

(*--------------------------------------------------------------------
  Initial state (Spec's Init)
--------------------------------------------------------------------*)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Init"

(*--------------------------------------------------------------------
  Next-action (Step and Done)
--------------------------------------------------------------------*)
Step ==
  /\ pc = "Init"
  /\ frontier # {}
  /\ \E n \in frontier :
        /\ marked' = marked \cup {n}
        /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
        /\ pc' = "Step"
Next ==
  \/ Step
  \/ /\ pc = "Step"
     /\ frontier = {}
     /\ marked' = marked
     /\ frontier' = frontier
     /\ pc' = "Done"
  \/ /\ pc = "Done"
     /\ UNCHANGED <<marked, frontier, pc>>

(*--------------------------------------------------------------------
  Specification (temporal formula)
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*--------------------------------------------------------------------
  Algorithm invariants (as described in the natural-language spec)
--------------------------------------------------------------------*)
Inv1 == \A n \in marked : (n \in Nodes)

Inv2 == \A n \in marked : 
          n = Root \/ \E m \in Nodes :
                /\ m \in marked
                /\ n \in Succ[m]

Inv3 == \A n \in marked :
          \E seq \in Seq :
            /\ Len(seq) >= 1
            /\ seq[1] = Root
            /\ seq[Len(seq)] = n
            /\ \A i \in 1..(Len(seq)-1) : seq[i+1] \in Succ[seq[i]]

PartialCorrectness == pc = "Done" => marked = Nodes

(*--------------------------------------------------------------------
  Liveness property
--------------------------------------------------------------------*)
Termination == []<>(pc = "Done")

=============================================================================