---- MODULE ReachableProofs ----
EXTENDS Naturals, Reachable, ReachableProofCore

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
    UNION { ReachableFrom(Sig) : Sig \in S }

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Working"

ExpandStep(n) ==
    /\ pc = "Working"
    /\ n \in frontier
    /\ n \notin marked
    /\ marked' = marked \cup {n}
    /\ frontier' = (frontier \ {n}) \cup Succ(n)
    /\ UNCHANGED pc

Backtrack ==
    /\ pc = "Working"
    /\ frontier = {}
    /\ frontier' = {Root}
    /\ marked' = {}
    /\ UNCHANGED pc

Terminate ==
    /\ pc = "Working"
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

Restart ==
    /\ pc = "Done"
    /\ pc' = "Working"
    /\ UNCHANGED <<marked, frontier>>

InitA == Init
NextA == ExpandStep(n) \/ Backtrack \/ Terminate \/ Restart

Spec == InitA /\ [][NextA]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Working", "Done"}
    /\ (Nodes \ Reachable \subseteq marked \cup frontier)

UnmarkedSuccessorsPropagate ==
    \A n \in marked : Succ(n) \subseteq (marked \cup frontier)

Invariant2 == ReachableFrom(marked \cup frontier) = Reachable

Invariant3 == ReachableFrom(Root) = (marked \cup ReachableFrom(frontier))

PartialCorrectness == (pc = "Done") => (marked = Reachable)

====