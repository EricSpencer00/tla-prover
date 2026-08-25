---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Nodes, Root, Succ

(* operator that the .cfg substitutes for Succ *)
ConnectedToSomeButNotAll(n) == Succ[n]

(* finite version of Seq, used by the .cfg *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= 5 }

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"

Edge == { <<x, y>> : x \in Nodes /\ y \in Succ[x] }

Reach(S) == S \/ { y \in Nodes : \E x \in S : <<x, y>> \in TC(Edge) }

Next ==
    \/ /\ pc = "run"
       /\ frontier # {}
       /\ \E n \in frontier :
            /\ IF n \notin marked
                  THEN /\ marked'   = marked \cup {n}
                       /\ frontier' = frontier \cup Succ[n]
                  ELSE /\ marked'   = marked
                       /\ frontier' = frontier \ {n}
            /\ UNCHANGED pc
    \/ /\ pc = "run"
       /\ frontier = {}
       /\ pc' = "done"
       /\ UNCHANGED <<marked, frontier>>
    \/ /\ pc = "done"
       /\ UNCHANGED <<marked, frontier, pc>>

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ Root \in Nodes
    /\ pc \in {"run", "done"}

Inv1 == \A m \in marked : Succ[m] \subseteq marked \cup frontier

Inv2 == marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 == Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness == (pc = "done") => (marked = Reach({Root}))

Termination == [] ( (Finite(Reach({Root}))) => <> (pc = "done") )

====