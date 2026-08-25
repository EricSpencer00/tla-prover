---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANTS
    Nodes,      \* The set of all nodes in the graph
    Root,       \* The distinguished root node (must be in Nodes)
    Succ        \* A function mapping each node to its set of successors

(*-----------------------------------------------------------------
  Operator substituted for Succ by the .cfg
-----------------------------------------------------------------*)
ConnectedToSomeButNotAll(n) == Succ[n]

(*-----------------------------------------------------------------
  Limited version of Seq (bounded length sequences)
-----------------------------------------------------------------*)
CONSTANT MaxLen \* Upper bound on sequence length, must be a natural number
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxLen }

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Relation used for reachability
-----------------------------------------------------------------*)
Rel == { <<x, y>> : x \in Nodes /\ y \in ConnectedToSomeButNotAll(x) }

Reach(S) ==
    S \cup { y \in Nodes : \E x \in S : <<x, y>> \in TC(Rel) }

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next ==
    \/ \E n \in frontier :
          /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup ConnectedToSomeButNotAll(n)
          /\ pc' = "run"
    \/ \E n \in frontier :
          /\ n \in marked
          /\ marked' = marked
          /\ frontier' = frontier \ {n}
          /\ pc' = "run"
    \/ /\ frontier = {}
       /\ pc = "run"
       /\ pc' = "done"
       /\ UNCHANGED <<marked, frontier>>

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "done"}

Inv1 ==
    \A n \in marked :
        ConnectedToSomeButNotAll(n) \subseteq marked \cup frontier

Inv2 ==
    marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 ==
    Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
    /\ frontier = {}
    /\ pc = "done"
    => marked = Reach({Root})

(*-----------------------------------------------------------------
  Liveness property (termination)
-----------------------------------------------------------------*)
Termination == <>[](frontier = {})

(*-----------------------------------------------------------------
  Exported identifiers
-----------------------------------------------------------------*)
THEOREM Spec => []TypeOK
THEOREM Spec => []Inv1
THEOREM Spec => []Inv2
THEOREM Spec => []Inv3
THEOREM Spec => []PartialCorrectness
THEOREM Spec => Termination

=============================================================================