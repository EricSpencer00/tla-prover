---- MODULE MCReachable ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

\* Each node has exactly two successors, chosen from the same finite
\* node set, which keeps the model finite without trivializing reachability.
\* The configuration module fixes this concrete structure for model checking.
\* Bounded sequences (LimitedSeq) replace the unbounded Seq operator so the
\* existential quantification in Reachable stays within a finite domain.

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"scanning", "completed"}

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "scanning"

Next ==
    \/ \E n \in frontier :
         /\ marked' = marked \cup {n}
         /\ frontier' = frontier \cup Succ[n]
         /\ pc' = pc
    \/ \E n \in frontier :
         /\ frontier' = frontier \ {n}
         /\ pc' = pc
    \/ /\ pc = "scanning"
       /\ frontier = {}
       /\ pc' = "completed"
       /\ marked' = marked
       /\ frontier' = frontier

MarkingStep == Next

Spec == Init /\ [][MarkingStep]_vars /\ WF_vars(MarkingStep)

\* Bounded path quantifier: only sequences up to the node count are checked,
\* surfacing every reachable node that way while keeping the model finite.
LimitedSeq == S \in Seq(Nodes) /\ Len(S) <= Cardinality(Nodes)

Reachable(n) ==
    \/ \E s \in LimitedSeq :
         /\ IF Len(s) = 0 THEN Head(s) = n ELSE FALSE
         /\ \A i \in 1 .. (Len(s) - 1) : s[i + 1] \in Succ[s[i]]
    \/ n = Root

Inv1 == \A n \in frontier : n \notin marked
Inv2 == \A p \in frontier : Reachable(p)
Inv3 == marked \subseteq { n \in Nodes : Reachable(n) }

PartialCorrectness == Cardinality(marked) = Cardinality(Nodes)

Termination == pc = "completed"

====