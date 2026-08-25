---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

\* Operator that will be substituted for Succ in the cfg
ConnectedToSomeButNotAll(n) == Succ[n]

\* Finite version of Seq for model checking
LimitedSeq(S) == Seq(S)

VARIABLES marked, frontier, pc

\* Type correctness invariant
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "done"}

\* Reachability operator using finite sequences
Reach(S) ==
    S \cup { n \in Nodes :
        \E p \in LimitedSeq(Nodes) :
            /\ Len(p) >= 1
            /\ p[1] \in S
            /\ \A i \in 1..Len(p)-1 : p[i+1] \in Succ[p[i]]
            /\ n = p[Len(p)] }

\* Initial state
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"
    /\ TypeOK

\* Main step
Step ==
    \/ /\ pc = "run"
       /\ frontier # {}
       /\ \E n \in frontier:
            /\ IF n \notin marked
                 THEN /\ marked'   = marked \cup {n}
                      /\ frontier' = frontier \cup Succ[n]
                 ELSE /\ marked'   = marked
                      /\ frontier' = frontier \ {n}
            /\ pc' = "run"
    \/ /\ pc = "run"
       /\ frontier = {}
       /\ pc' = "done"
       /\ UNCHANGED << marked, frontier >>

Next == Step

\* Specification
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* Invariants
Inv1 == \A m \in marked : Succ[m] \subseteq marked \cup frontier

Inv2 == (marked \cup Reach(frontier)) = Reach(marked \cup frontier)

Inv3 == Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness == frontier = {} => marked = Reach({Root})

\* Liveness property
Termination == <> (frontier = {})

====