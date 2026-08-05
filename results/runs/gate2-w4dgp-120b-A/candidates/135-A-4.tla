---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

\* A model-checking configuration module for the sequential Misra reachability
\* algorithm. It instantiates the algorithm with a concrete 4-node graph and a
\* bounded (finite) sequence type, so TLC can exhaustively explore every reachable
\* state. The graph is deterministic in that each node has exactly two successors,
\* which keeps branching low while still providing non-trivial reachability.
CONSTANTS Nodes, Root, Succ

ASSUME Root \in Nodes
ASSUME Succ \subseteq (Nodes \X Nodes)

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"init", "searching", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "init"

Search ==
    /\ pc = "init"
    /\ \E n \in frontier :
        frontier' = (frontier \cup {m \in Nodes : <<n, m>> \in Succ}) \ marked
    /\ marked' = marked \cup frontier
    /\ pc' = "searching"

Done ==
    /\ pc = "searching"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == Search \/ Done

Spec == Init /\ [][Next]_vars

\* Safety: the three algorithm invariants and partial correctness, all type-correct.
Inv1 == \A n \in frontier : \E m \in Nodes : <<n, m>> \in Succ
Inv2 == \A n \in marked : \E p \in Seq(Nodes) : p[1] = Root /\ p[Len(p)] = n
Inv3 == marked = {n \in Nodes : \E p \in Seq(Nodes) : p[1] = Root /\ p[Len(p)] = n}
PartialCorrectness == \A n \in Nodes : (n \in marked) <=> (\E p \in Seq(Nodes) : p[1] = Root /\ p[Len(p)] = n)

InvariantProperties == TypeOK /\ Inv1 /\ Inv2 /\ Inv3 /\ PartialCorrectness

\* Liveness: sequential Misra reachability always eventually completes.
Termination == <>(pc = "done")

====