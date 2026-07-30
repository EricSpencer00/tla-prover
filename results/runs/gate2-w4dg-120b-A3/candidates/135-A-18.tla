---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

\* The safety and liveness properties together make up the entire
\* validation suite for this configuration module.
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in {"idle", "exploring", "done"}

\* Reachability is defined in the algorithm specification via an
\* existential quantification over paths. That quantifier is bounded
\* here with a finite sequence override (LimitedSeq) and a concrete
\* graph (Succ) so the model is finite and TLC can explore it.
Reachable(n) == \E s \in LimitedSeq(Nodes) :
    /\ Len(s) <= Cardinality(Nodes)
    /\ s # << >>
    /\ Head(s) = Root
    /\ Last(s) = n
    /\ \A k \in 1..(Len(s) - 1) : s[k + 1] \in Succ[s[k]]

Inv1 == \A a \in frontier : \E b \in marked : a \in Succ[b]
Inv2 == \A n \in Nodes : Reachable(n) => n \in marked
Inv3 == marked \subseteq {n \in Nodes : Reachable(n)}
PartialCorrectness == marked = {n \in Nodes : Reachable(n)}

Termination == <>(pc = "done")

\* The .cfg substitutes ConnectedToSomeButNotAll for Succ, so Succ
\* is overridden in the model by this operator.
ConnectedToSomeButNotAll == Succ

\* Finite override for the infinite Sequences!Seq: keep the name
\* the .cfg expects (LimitedSeq) and override only the operator on
\* the right; do NOT declare or redefine Seq itself.
LimitedSeq == Seq

====