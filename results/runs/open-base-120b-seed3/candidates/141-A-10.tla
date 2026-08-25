---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Nodes, Root, Succ

\*--- Operators substituted by the cfg ---------------------------------
ConnectedToSomeButNotAll(n) == Succ(n)

LimitedSeq(S) == Seq(S) \* a finite version of Seq (Seq already yields finite sequences)

\*--- State variables --------------------------------------------------
VARIABLES marked, frontier, pc

\*--- Helper definitions -----------------------------------------------
SuccRel == { <<x, y>> : x \in Nodes /\ y \in Succ(x) }

Reach(S) == { y \in Nodes : \E x \in S : <<x, y>> \in TC(SuccRel) } \cup S

\*--- Initial state ----------------------------------------------------
Init == 
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"

\*--- Main action (pick a node from frontier) -------------------------
MainAction ==
    /\ pc = "Run"
    /\ frontier # {}
    /\ \E n \in frontier :
        \/ /\ n \notin marked
           /\ marked'   = marked \cup {n}
           /\ frontier' = frontier \cup ConnectedToSomeButNotAll(n)
           /\ pc'       = pc
        \/ /\ n \in marked
           /\ marked'   = marked
           /\ frontier' = frontier \ {n}
           /\ pc'       = pc

\*--- Termination action (frontier empty) -------------------------------
Terminate ==
    /\ pc = "Run"
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

\*--- Next relation ----------------------------------------------------
Next == MainAction \/ Terminate \/ UNCHANGED <<marked, frontier, pc>>

\*--- Specification ----------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\*--- Invariants -------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Run", "Done"}

Inv1 ==
    \A n \in marked : Succ(n) \subseteq marked \cup frontier

Inv2 ==
    marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 ==
    Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
    (pc = "Done") => (marked = Reach({Root}))

\*--- Liveness property ------------------------------------------------
Termination == <> (pc = "Done")

\*--- The list of identifiers required by the .cfg ----------------------
\* (these are already defined with the exact names above)

====