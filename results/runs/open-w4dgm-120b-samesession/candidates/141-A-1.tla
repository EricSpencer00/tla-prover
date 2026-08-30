---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences
CONSTANTS Nodes, Root, Succ

TypeOK ==
    /\ Nodes \subseteq Nat
    /\ Root \in Nodes /\ Succ \in [Nodes -> SUBSET Nodes]
    /\ UNCHANGED Nodes

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

Explore(n) ==
    /\ n \in frontier
    /\ IF n \notin marked
         THEN /\ marked' = marked \cup {n}
              /\ frontier' = frontier \cup Succ[n]
         ELSE /\ frontier' = frontier \ {n}
              /\ marked' = marked
    /\ pc' = "running"

Terminate ==
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == \E n \in Nodes : Explore(n) \/ Terminate

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Explore(FrontierChoice))
    /\ SF_vars(Terminate)

FrontierChoice == CHOOSE e \in frontier : TRUE

Inv1 ==
    /\ \A n \in Nodes :
         n \in marked => (Succ[n] \subseteq marked \cup frontier)
    /\ \A n \in Nodes : (n \in frontier) => (n \in Nodes)

Inv2 ==
    /\ (marked \cup frontier) = Nodes
    /\ (marked \cup frontier) = (marked \cup (UNION {Succ[n] : n \in frontier}))

Inv3 ==
    /\ marked \cup (UNION {Succ[n] : n \in frontier}) = Nodes
    /\ \A n \in frontier : n \in Nodes

PartialCorrectness == Inv2 /\ Inv3

Termination == (frontier # {}) ~> (frontier = {})

\* Replacements the .cfg makes: Succ is overridden by ConnectedToSomeButNotAll,
\* and the finite version of Seq (LimitedSeq) is overridden by Seq from Sequences.
ConnectedToSomeButNotAll(n) == Succ[n]
LimitedSeq(S) == IF Cardinality(S) < 2 THEN Seq(S) ELSE CHOOSE s \in Seq(S) : TRUE

====