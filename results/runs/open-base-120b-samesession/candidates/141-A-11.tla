---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Nodes,   \* The set of all graph nodes
    Root,    \* The distinguished start node (Root \\in Nodes)
    Succ     \* Successor function: [n \\in Nodes |-> SUBSET Nodes]

\*--------------------------------------------------------------------
\* Auxiliary definitions
\*--------------------------------------------------------------------
SuccRel == { <<n, m>> : n \\in Nodes /\ m \\in Succ[n] }

Reach(S) == 
    (* Nodes reachable from any node in S via zero or more Succ steps *)
    S \\cup { y \\in Nodes : 
                \\E x \\in S : <<x, y>> \\in TC(SuccRel) }

\*--------------------------------------------------------------------
\* Variables
\*--------------------------------------------------------------------
VARIABLES marked, frontier, pc

Vars == <<marked, frontier, pc>>

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"
    /\ Root \\in Nodes

\*--------------------------------------------------------------------
\* Main transition
\*--------------------------------------------------------------------
MainAction ==
    /\ frontier # {}
    /\ \\E n \\in frontier :
        IF n \\notin marked THEN
            /\ marked' = marked \\cup {n}
            /\ frontier' = frontier \\cup Succ[n]
            /\ pc' = pc
        ELSE
            /\ marked' = marked
            /\ frontier' = frontier \\ {n}
            /\ pc' = pc
        /\ UNCHANGED <<>>  \* no other variables change

TerminateAction ==
    /\ frontier = {}
    /\ pc = "running"
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ MainAction
    \/ TerminateAction

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_Vars /\ WF_Vars(Next)

\*--------------------------------------------------------------------
\* Invariants
\*--------------------------------------------------------------------
TypeOK ==
    /\ marked \\subseteq Nodes
    /\ frontier \\subseteq Nodes
    /\ pc \\in {"running", "done"}

Inv1 ==
    \A m \\in marked :
        Succ[m] \\subseteq marked \\cup frontier

Inv2 ==
    marked \\cup Reach(frontier) = Reach(marked \\cup frontier)

Inv3 ==
    Reach({Root}) = marked \\cup Reach(frontier)

PartialCorrectness ==
    /\ pc = "done"
    => marked = Reach({Root})

\*--------------------------------------------------------------------
\* Liveness property
\*--------------------------------------------------------------------
Termination == <> (pc = "done")

\*--------------------------------------------------------------------
\* Operators required by the configuration
\*--------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == {}  \* placeholder; the .cfg will substitute this for Succ

LimitedSeq(S) == 
    LET MaxLen == 5 IN
    { s \\in Seq(S) : Len(s) <= MaxLen }

============================================================================