---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

(*-----------------------------------------------------------------
  Types and auxiliary definitions
-----------------------------------------------------------------*)
NodeSet == Nodes

MarkSet == marked
FrontierSet == frontier

Succs(n) == Succ[n]

(* reachable nodes from a set S via successors in the graph *)
Reach(S) == 
    LET Rec == [reach \in [Node -> BOOLEAN] |-> 
                    ( \A n \in NodeSet :
                        reach[n] = (n \in S) \/
                        (\E m \in NodeSet : reach[m] /\ n \in Succs(m)) )
               ]
    IN { n \in NodeSet : Rec[n] }

(*-----------------------------------------------------------------
  State predicates
-----------------------------------------------------------------*)
TypeOK == 
    /\ marked \in SUBSET NodeSet
    /\ frontier \in SUBSET NodeSet
    /\ pc \in {"Running", "Done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Running"

(*-----------------------------------------------------------------
  Main action
-----------------------------------------------------------------*)
ProcessStep ==
    \/ \E n \in frontier :
          /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succs(n)
          /\ pc' = pc
    \/ \E n \in frontier :
          /\ n \in marked
          /\ marked' = marked
          /\ frontier' = frontier \ {n}
          /\ pc' = pc
    \/ /\ frontier = {}
          /\ pc = "Running"
          /\ pc' = "Done"
          /\ UNCHANGED <<marked, frontier>>

Next == ProcessStep

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
Inv1 == \A n \in marked : Succs(n) \subseteq marked \cup frontier

Inv2 == 
    (Reach(marked) \cup Reach(frontier)) = Reach(marked \cup frontier)

Inv3 == 
    Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness == 
    /\ pc = "Done"
    /\ marked = Reach({Root})

Termination == 
    <> (pc = "Done")

=============================================================================