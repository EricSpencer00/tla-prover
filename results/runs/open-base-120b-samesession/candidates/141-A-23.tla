---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANTS
    Nodes,               \* The set of all graph nodes
    Root,                \* The distinguished root node
    Succ                 \* Successor function: [Nodes -> SUBSET Nodes]

(*-----------------------------------------------------------------
  Operator substitution (overridden by the .cfg)
-----------------------------------------------------------------*)
ConnectedToSomeButNotAll(n) == Succ[n]

(*-----------------------------------------------------------------
  Finite version of Seq (replaces Seq from Sequences)
-----------------------------------------------------------------*)
CONSTANT MaxSeqLen \* bound on sequence length for model checking
LimitedSeq == { s \in Seq(Nodes) : Len(s) <= MaxSeqLen }

(*-----------------------------------------------------------------
  Derived relations and reachability operators
-----------------------------------------------------------------*)
SuccRel == { <<a, b>> : a \in Nodes /\ b \in Succ[a] }

Reach(S) == 
    LET
        R == { y \in Nodes : 
                \E x \in S : <<x, y>> \in TC(SuccRel) }
    IN  R \cup S

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Initialization
-----------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
PickNode == CHOOSE n \in frontier

Next ==
    \E n \in frontier :
        \/ /\ n \notin marked
           /\ marked' = marked \cup {n}
           /\ frontier' = frontier \cup Succ[n]
           /\ pc' = IF frontier' = {} THEN "Done" ELSE "Run"
        \/ /\ n \in marked
           /\ marked' = marked
           /\ frontier' = frontier \ {n}
           /\ pc' = IF frontier' = {} THEN "Done" ELSE "Run"

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(*-----------------------------------------------------------------
  Type-correctness invariant
-----------------------------------------------------------------*)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Run", "Done"}

(*-----------------------------------------------------------------
  Safety invariants
-----------------------------------------------------------------*)
Inv1 ==
    \A n \in marked : ConnectedToSomeButNotAll[n] \subseteq marked \cup frontier

Inv2 ==
    (marked \cup Reach(frontier)) = Reach(marked \cup frontier)

Inv3 ==
    Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
    /\ pc = "Done"
    /\ marked = Reach({Root})

(*-----------------------------------------------------------------
  Liveness property
-----------------------------------------------------------------*)
Termination == <> (pc = "Done")

(*-----------------------------------------------------------------
  The full specification for the model checker
-----------------------------------------------------------------*)
THEOREM Spec => []TypeOK
THEOREM Spec => []Inv1
THEOREM Spec => []Inv2
THEOREM Spec => []Inv3
THEOREM Spec => []PartialCorrectness
THEOREM Spec => Termination

====