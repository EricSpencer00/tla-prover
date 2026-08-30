---- MODULE ReachableProofs ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Root

ASSUME Root \in Nodes

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
    IF S = {} THEN {}
    ELSE LET n == CHOOSE x \in S : TRUE IN
         {n} \cup ReachableFrom({m \in Nodes : m \in ReachableFrom(S \ {n}) \/ \E e \in Edges : e.from = n /\ e.to = m})

NodeEdges(n) == {e \in Edges : e.from = n}

RECURSIVE FrOn(_)
FrOn(S) ==
    IF S = {} THEN {}
    ELSE LET n == CHOOSE x \in S : TRUE IN
         NodeEdges(n) \cup FrOn({m \in Nodes : m \in FrOn(S \ {n}) \/ \E e \in Edges : e.from = n /\ e.to = m})

CONSTANTS Edges

Lemma1 == FrOn({Root}) = ReachableFrom({Root})
Lemma2 == \A X \in SUBSET Nodes : X \subseteq ReachableFrom({Root}) => ReachableFrom(X) \subseteq ReachableFrom({Root})
Lemma3 == ReachableFrom({}) = {}

Init ==
    /\ marked = {Root}
    /\ frontier = NodeEdges(Root)
    /\ pc = 0

Mark ==
    /\ frontier # {}
    /\ \E e \in frontier :
         /\ frontier' = frontier \ {e}
         /\ marked' = marked \cup {e.to}
    /\ pc' = 1

ExpandFrontier ==
    /\ frontier # {}
    /\ \E e \in frontier :
         /\ frontier' = (frontier \ {e}) \cup NodeEdges(e.to)
    /\ pc' = 2
    /\ marked' = marked

Terminate ==
    /\ frontier = {}
    /\ pc' = 3
    /\ UNCHANGED <<marked, frontier>>

Next == Mark \/ ExpandFrontier \/ Terminate

Spec == Init /\ [][Next]_vars

TypeAndClosure ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Edges
    /\ \A e \in frontier : e.from \in marked
    /\ \A n \in marked : \A e \in NodeEdges(n) : e.to \in marked \/ e \in frontier

FrFrontierMarking ==
    (marked \cup ReachableFrom(frontier)) = ReachableFrom({Root})

MarkFrontierExact ==
    ReachableFrom({Root}) = (marked \cup ReachableFrom(frontier))

TerminatingStateReachesAll == (frontier = {}) => (marked = ReachableFrom({Root}))

Invariants == TypeAndClosure /\ FrFrontierMarking /\ MarkFrontierExact

Properties == TerminatingStateReachesAll

====