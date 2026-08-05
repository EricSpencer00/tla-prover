---- MODULE ReachableProofs ----
EXTENDS Naturals, Reachable

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

RECURSIVE ReachFrom(_, _)
ReachFrom(S, T) == IF T = {} THEN {} ELSE LET n == CHOOSE x \in T : TRUE IN S[n] \cup ReachFrom(S, S[n]) \cup ReachFrom(S, T \ {n})

AllNodes == ReachFrom([n \in Nodes |-> {}], Nodes)

Init == /\ marked = {Root}
        /\ frontier = {}
        /\ pc = "spanning"

Explore == /\ \E n \in frontier :
             /\ frontier' = frontier \ {n}
             /\ marked' = marked \cup {n}
             /\ frontier' = frontier' \cup (ReachFrom([m \in Nodes |-> IF m = n THEN {n} ELSE {}], {n}) \ marked)
        /\ pc' = pc
MarkFrontier == /\ frontier = {}
                /\ \E n \in marked :
                     frontier' = frontier \cup (ReachFrom([m \in Nodes |-> IF m = n THEN {n} ELSE {}], {n}) \ marked)
                /\ pc' = pc
Finalize == /\ frontier = {}
            /\ \A n \in marked : ReachFrom([m \in Nodes |-> IF m = n THEN {n} ELSE {}], {n}) \subseteq marked
            /\ pc' = "spanning"
Idle == /\ pc = "spanning"
        /\ frontier = {}
        /\ \A n \in marked : ReachFrom([m \in Nodes |-> IF m = n THEN {n} ELSE {}], {n}) \subseteq marked
        /\ pc' = "spanning"
        /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ MarkFrontier \/ Finalize \/ Idle

Spec == Init /\ [][Next]_vars

TypeOK == /\ marked \subseteq Nodes /\ frontier \subseteq Nodes /\ pc \in {"spanning"}

MarkedFrontierOK == \A n \in marked : ReachFrom([m \in Nodes |-> IF m = n THEN {n} ELSE {}], {n}) \subseteq marked \cup frontier

MarkedReachable == marked \cup ReachFrom([n \in Nodes |-> ReachFrom([m \in Nodes |-> IF m = n THEN {n} ELSE {}], {n}) \ marked], frontier) = ReachFrom([n \in Nodes |-> {}], Nodes)

Spanning == ReachFrom([n \in Nodes |-> {}], Nodes) = marked

TypeOKInductive == TypeOK /\ MarkedFrontierOK
InductionByLemma1 == MarkedFrontierOK
InductionByLemma2 == MarkedReachable
PartialCorrectness == Finalize => Spanning

====