---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

\* Edge relation of the directed graph
Edge == { <<n, m>> : n \in Nodes /\ m \in Succ[n] }

\* Nodes reachable from a set S (including S itself)
ReachFrom(S) == 
    S \cup { n \in Nodes : \E s \in S : <<s, n>> \in TC(Edge) }

\* Nodes reachable from the root
Reachable == ReachFrom({Root})

\* Initial state
Init == 
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"

\* Main transition: pick a node from the frontier
MainAction ==
    \/ /\ frontier # {}
       /\ \E n \in frontier :
            /\ IF n \notin marked THEN
                 /\ marked' = marked \cup {n}
                 /\ frontier' = frontier \cup Succ[n]
               ELSE
                 /\ marked' = marked
                 /\ frontier' = frontier \ {n}
            /\ UNCHANGED pc
    \/ /\ frontier = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<marked, frontier>>

Next == MainAction

\* Full specification with weak fairness on the main action
Spec == Init /\ [][Next]_<<marked, frontier, pc>> /\ WF_vars(Next)

\* Type correctness invariant
TypeOK == 
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ Root \in Nodes

\* Invariant 1: successors of marked nodes are already marked or frontier
Inv1 == \A m \in marked : Succ[m] \subseteq marked \cup frontier

\* Invariant 2: marked ∪ ReachFrom(frontier) = ReachFrom(marked ∪ frontier)
Inv2 == (marked \cup ReachFrom(frontier)) = ReachFrom(marked \cup frontier)

\* Invariant 3: Reachable = marked ∪ ReachFrom(frontier)
Inv3 == Reachable = marked \cup ReachFrom(frontier)

\* Partial correctness: when terminated, marked = Reachable
PartialCorrectness == (pc = "Done") => (marked = Reachable)

\* Liveness property: eventual termination
Termination == <> (pc = "Done")

\* Operator substituted for Succ in the cfg
ConnectedToSomeButNotAll(n) == Succ[n]

\* Finite version of Seq (replaces Seq from Sequences)
LimitedSeq(S) == { s \in Seq(S) : Len(s) \in Nat }

====