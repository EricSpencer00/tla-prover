---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ

(*-----------------------------------------------------------------
   Operators required by the .cfg substitution
-----------------------------------------------------------------*)
ConnectedToSomeButNotAll == [ n \in Nodes |-> Succ[n] ]

(*-----------------------------------------------------------------
   A finite version of Seq for model checking
-----------------------------------------------------------------*)
LimitedSeq == { s \in Seq(Nodes) : Len(s) <= 5 }

(*-----------------------------------------------------------------
   Variables
-----------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*-----------------------------------------------------------------
   Helper definitions
-----------------------------------------------------------------*)
\* Succ as a binary relation
SuccRel == { <<n,m>> : n \in Nodes /\ m \in Succ[n] }

\* Nodes reachable from a set S (including S itself)
ReachFromSet(S) ==
  S \cup { n \in Nodes : \E r \in S : <<r,n>> \in TC(SuccRel) }

(*-----------------------------------------------------------------
   Type correctness invariant
-----------------------------------------------------------------*)
TypeOK == 
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Run", "Done"}

(*-----------------------------------------------------------------
   Invariant 1: successors of marked nodes are in marked ∪ frontier
-----------------------------------------------------------------*)
Inv1 ==
    \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

(*-----------------------------------------------------------------
   Invariant 2: closure property of marked ∪ frontier
-----------------------------------------------------------------*)
Inv2 ==
    (marked \cup ReachFromSet(frontier)) = ReachFromSet(marked \cup frontier)

(*-----------------------------------------------------------------
   Invariant 3: reachable from Root equals marked ∪ reachable from frontier
-----------------------------------------------------------------*)
Inv3 ==
    ReachFromSet({Root}) = marked \cup ReachFromSet(frontier)

(*-----------------------------------------------------------------
   Partial correctness: when finished, marked equals reachable set
-----------------------------------------------------------------*)
PartialCorrectness ==
    frontier = {} => marked = ReachFromSet({Root})

(*-----------------------------------------------------------------
   Initialization
-----------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"
    /\ TypeOK

(*-----------------------------------------------------------------
   Next-state relation
-----------------------------------------------------------------*)
Next ==
    \/ /\ pc = "Run"
       /\ frontier = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<marked, frontier>>
    \/ /\ pc = "Run"
       /\ frontier # {}
       /\ \E n \in frontier :
            ( /\ n \notin marked
               /\ marked' = marked \cup {n}
               /\ frontier' = frontier \cup Succ[n]
               /\ UNCHANGED pc
            )
            \/ ( /\ n \in marked
               /\ frontier' = frontier \ {n}
               /\ UNCHANGED <<marked, pc>> )
    \/ /\ pc = "Done"
       /\ UNCHANGED <<marked, frontier, pc>>

(*-----------------------------------------------------------------
   Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*-----------------------------------------------------------------
   Invariants list (for the .cfg file)
-----------------------------------------------------------------*)
INVARIANT TypeOK
INVARIANT Inv1
INVARIANT Inv2
INVARIANT Inv3
INVARIANT PartialCorrectness

(*-----------------------------------------------------------------
   Liveness property: eventual termination
-----------------------------------------------------------------*)
Termination == <> (frontier = {})

=============================================================================