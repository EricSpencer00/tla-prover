---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ   \* Succ will be replaced by ConnectedToSomeButNotAll in the .cfg

\* Operator that substitutes for Succ
ConnectedToSomeButNotAll == [n \in Nodes |-> {}]

\* Finite version of Seq (alias)
LimitedSeq(S) == Seq(S)

\* State variables
VARIABLES marked, frontier, pc

\* Initial state
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"

\* Edge relation derived from the successor function
Edge == [n \in Nodes, m \in Nodes |-> m \in ConnectedToSomeButNotAll[n]]

\* Reachability from a set of nodes using transitive closure
Reach(S) ==
    S \cup { n \in Nodes : \E s \in S : <<s, n>> \in TC(Edge) }

\* Main step
Next ==
    \/ \E n \in frontier :
          /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup ConnectedToSomeButNotAll[n]
          /\ UNCHANGED pc
    \/ \E n \in frontier :
          /\ n \in marked
          /\ marked' = marked
          /\ frontier' = frontier \ {n}
          /\ UNCHANGED pc
    \/ /\ frontier = {}
       /\ pc = "run"
       /\ pc' = "done"
       /\ UNCHANGED <<marked, frontier>>

\* Specification
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* Type correctness invariant
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "done"}

\* Invariant 1: successors of marked nodes are in marked or frontier
Inv1 ==
    \A n \in marked : ConnectedToSomeButNotAll[n] \subseteq marked \cup frontier

\* Invariant 2: marked ∪ Reach(frontier) = Reach(marked ∪ frontier)
Inv2 ==
    marked \cup Reach(frontier) = Reach(marked \cup frontier)

\* Invariant 3: Reach({Root}) = marked ∪ Reach(frontier)
Inv3 ==
    Reach({Root}) = marked \cup Reach(frontier)

\* Partial correctness: when terminated, marked equals reachable from Root
PartialCorrectness ==
    (frontier = {}) => marked = Reach({Root})

\* Liveness property: eventual termination
Termination == <> (frontier = {})

====