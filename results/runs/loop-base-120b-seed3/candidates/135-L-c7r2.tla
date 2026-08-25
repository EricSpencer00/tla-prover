---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Nodes, Root, Succ

(*--- Bounded sequence operator (replaces Seq) -------------------*)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(*--- Operator substituting for Succ -------------------------------*)
ConnectedToSomeButNotAll == Succ

VARIABLES marked, frontier, pc

(*--- Initial state -----------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"

(*--- Next-state relation ------------------------------------------*)
Next ==
    \/ /\ pc = "run"
       /\ \E n \in frontier :
            /\ marked'   = marked \cup {n} \cup ConnectedToSomeButNotAll[n]
            /\ frontier' = (frontier \ {n}) \cup (ConnectedToSomeButNotAll[n] \ marked')
            /\ pc'       = IF frontier' = {} THEN "done" ELSE "run"
    \/ /\ pc = "done"
       /\ UNCHANGED <<marked, frontier, pc>>

(*--- Specification ------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*--- Type correctness invariant -----------------------------------*)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "done"}

(*--- Reachable nodes defined via transitive closure ---------------*)
SuccRel == { <<n, m>> : n \in Nodes /\ m \in ConnectedToSomeButNotAll[n] }

Reachable ==
    { n \in Nodes : <<Root, n>> \in TC(SuccRel) } \cup {Root}

(*--- Invariant 1: successor closure -------------------------------*)
Inv1 ==
    \A n \in marked : ConnectedToSomeButNotAll[n] \subseteq marked

(*--- Invariant 2: all marked nodes are reachable -----------------*)
Inv2 ==
    marked \subseteq Reachable

(*--- Invariant 3: marked set equals the reachable set -----------*)
Inv3 ==
    marked = Reachable

(*--- Partial correctness property --------------------------------*)
PartialCorrectness ==
    (pc = "done") => (frontier = {} /\ marked = Reachable)

(*--- Liveness property: termination -------------------------------*)
Termination == <> (pc = "done")

====