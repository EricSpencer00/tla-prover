---- MODULE ReachableProofs ----
EXTENDS Integers, FiniteSets, Reachable

CONSTANTS Nodes, Root

\* The proof module re-exposes the algorithm's spec so it can be checked with
\* TLAPS, and adds the graph-theoretic lemmas that the invariants depend on.
Spec = \A ReachableSpec
Init == ReachableSpec!Init
Next == ReachableSpec!Next

TypeOK ==
    /\ ReachableSpec!TypeOK
    /\ \A n \in Nodes : Cardinality(Successors(n)) <= Cardinality(Nodes)

\* Invariant 1 adds the frontier/marked successor disjointness to the
\* algorithm's own per-step type check.
Invariant1 ==
    /\ TypeOK
    /\ \A n \in Nodes : (n \in ReachableSpec!Marked) => Successors(n) \subseteq (ReachableSpec!Marked \cup ReachableSpec!Frontier)

\* Reachable-from is monotone under forward edges; this lemma is the
\* combinatorial fact the two equivalence invariants below both rely on.
Lemma1 ==
    \A A \in SUBSET Nodes :
        ReachableFrom(A) = A \cup { y \in Nodes : \E n \in A : y \in Successors(n) }

Invariant2 ==
    \A n \in Nodes : Successors(n) \subseteq ReachableSpec!Marked \cup ReachableSpec!Frontier
    /\ ReachableFrom(ReachableSpec!Marked) \cup ReachableFrom(ReachableSpec!Frontier) = ReachableFrom(ReachableSpec!Marked \cup ReachableSpec!Frontier)

Lemma2 == \A n \in Nodes : Successors(n) \subseteq ReachableFrom({n})

Lemma3 == ReachableFrom({}) = {}

Invariant3 ==
    /\ Lemma2
    /\ Lemma3
    /\ ReachableFrom({Root}) = ReachableSpec!Marked \cup ReachableFrom(ReachableSpec!Frontier)

\* Partial correctness: no liveness reasoning, just the coupling of the
\* frontier/marked bookkeeping with the true reachable set.
TerminationSound ==
    /\ (ReachableSpec!Pc = "halt") => (ReachableFrom({Root}) = ReachableSpec!Marked)

INVARIANTS == Invariant1 /\ Invariant2 /\ Invariant3
PROPERTIES == TerminationSound
====