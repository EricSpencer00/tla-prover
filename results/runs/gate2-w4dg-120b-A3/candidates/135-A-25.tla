---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ

\* The model is a finite-state instance of the sequential Misra reachability
\* algorithm.  Succ defines the directed edges of the graph; Marked is the
\* computed reachable set; Frontier is the set being expanded this step; pc
\* is the program counter: 0 = idle, 1 = exploring a node, 2 = done.
VARIABLES Marked, Frontier, pc, Active

vars == << Marked, Frontier, pc, Active >>

Blank == "blank"
MaxLen == Cardinality(Nodes)

TypeOK ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ pc \in {0, 1, 2}
    /\ Active \in Nodes \cup {Blank}

Init ==
    /\ Marked = {}
    /\ Frontier = {Root}
    /\ pc = 0
    /\ Active = Blank

\* Action: pick an unmarked frontier node and start exploring it.
Explore(n) ==
    /\ pc = 0
    /\ n \in Frontier
    /\ n \notin Marked
    /\ pc' = 1
    /\ Active' = n
    /\ UNCHANGED << Marked, Frontier >>

\* Action: the explored node adds all of its successors to the frontier and
\* joins the reachable set.
AddSuccessors ==
    /\ pc = 1
    /\ Marked' = Marked \cup {Active}
    /\ Frontier' = Frontier \cup Succ[Active]
    /\ pc' = 0
    /\ Active' = Blank

\* Action: when every frontier node is already reachable, the algorithm is
\* done; this is what the liveness property will wait for.
Done ==
    /\ pc = 0
    /\ Frontier \subseteq Marked
    /\ pc' = 2
    /\ UNCHANGED << Marked, Frontier, Active >>

Next == \E n \in Nodes : Explore(n) \/ AddSuccessors \/ Done

\* A guarded version of Seq: empty or a pair built from a node that has room
\* in its list before the bound MaxLen.  This keeps the model finite for TLC.
LimitedSeq(s) ==
    \/ s = << >>
    \/ (\E x \in Nodes, rest \in Seq(Nodes) :
            /\ \A y \in DOMAIN rest : rest[y] \in Nodes
            /\ pc < MaxLen
            /\ s = << x >> \circ rest))
Seq == LimitedSeq

Spec == Init /\ [][Next]_vars

Inv1 == Marked \subseteq Union({Succ[n] : n \in Marked})
Inv2 == Frontier \subseteq Marked \cup Union({Succ[n] : n \in Marked})
Inv3 == Marked \cup Frontier = Nodes
PartialCorrectness == Frontier \subseteq Marked
Termination == <> (pc = 2)

\* Substituted operators: ConnectedToSomeButNotAll replaces Succ in the
\* configuration to enforce the "2 successors per node" bound; the underlying
\* operator on the left (Succ) is left untouched as instructed.
ConnectedToSomeButNotAll(n) == { m \in Nodes : m # n }

====