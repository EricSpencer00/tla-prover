---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

(*--- assumptions about the concrete graph -----------------------------------*)
ASSUME Nodes = 1..4
ASSUME Root \in Nodes
ASSUME Procs = {1, 2}
ASSUME Succ \in [Nodes -> SUBSET Nodes]

(* each node has exactly two successors (the concrete graph) *)
ASSUME \A n \in Nodes : Cardinality(Succ[n]) = 2

(*--- operators overridden by the .cfg --------------------------------------*)
ConnectedToSomeButNotAll(n) == { m \in Nodes : m # n }

LimitedSeq == { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

(*--- state variables --------------------------------------------------------*)
VARIABLES marked, frontier, pc, sel, succSet

vars == <<marked, frontier, pc, sel, succSet>>

(*--- initial state ----------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> 0]
    /\ sel = [p \in Procs |-> Root]
    /\ succSet = [p \in Procs |-> {}]

(*--- actions ---------------------------------------------------------------*)
Explore(p) ==
    /\ pc[p] = 0
    /\ LET n == sel[p] IN
         /\ n \in frontier
         /\ marked'   = marked \cup {n}
         /\ frontier' = (frontier \ {n}) \cup Succ[n]
         /\ pc'       = [pc EXCEPT ![p] = @ + 1]
         /\ sel'      = sel
         /\ succSet'  = succSet

Next ==
    \E p \in Procs : Explore(p)

(*--- specification ----------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*--- invariant -------------------------------------------------------------*)
Inv ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> Nat]
    /\ sel \in [Procs -> Nodes]
    /\ succSet \in [Procs -> SUBSET Nodes]
    /\ marked \cap frontier = {}

(*--- refinement property ----------------------------------------------------*)
Refines == TRUE

====