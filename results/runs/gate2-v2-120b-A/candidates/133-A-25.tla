---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, TLC

(*-----------------------------------------------------------------
  Constants required by the reference configuration
-----------------------------------------------------------------*)
CONSTANTS 
    Nodes,   \* The set of nodes in the graph (must be finite)
    Root,    \* The distinguished start node
    Procs,   \* The set of worker processes (e.g., {"p1","p2"})
    Succ,    \* Total function: [Nodes -> SUBSET Nodes] giving successors
    Seq      \* Upper bound on sequence lengths (equal to Cardinality(Nodes))

(*-----------------------------------------------------------------
  Derived constants
-----------------------------------------------------------------*)
NodeCount == Cardinality(Nodes)

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES 
    marked,        \* Set of nodes that have been discovered
    frontier,     \* Set of nodes currently being explored
    pc,            \* Program counter per process: [Procs -> {"idle","pick","expand"}]
    sel,           \* Currently selected node per process: [Procs -> Nodes \cup {None}]
    succSet        \* Successor set per process: [Procs -> SUBSET Nodes]

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
None == "none"

InitMarked == {Root}
InitFrontier == {}
InitPC == [p \in Procs |-> "idle"]
InitSel == [p \in Procs |-> None]
InitSuccSet == [p \in Procs |-> {}]

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ marked = InitMarked
    /\ frontier = InitFrontier
    /\ pc = InitPC
    /\ sel = InitSel
    /\ succSet = InitSuccSet

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
PickNode(p) ==
    /\ pc[p] = "idle"
    /\ frontier # {}
    /\ \E n \in frontier :
          /\ sel' = [sel EXCEPT ![p] = n]
          /\ frontier' = frontier \ {n}
          /\ pc' = [pc EXCEPT ![p] = "expand"]
          /\ succSet' = succSet
          /\ marked' = marked

Expand(p) ==
    /\ pc[p] = "expand"
    /\ \E n \in Nodes :
          /\ n = sel[p]
          /\ nw = Succ[n]
          /\ /\ frontier' = frontier \cup (nw \ marked)
             /\ marked' = marked \cup nw
          /\ pc' = [pc EXCEPT ![p] = "idle"]
          /\ sel' = [sel EXCEPT ![p] = None]
          /\ succSet' = [succSet EXCEPT ![p] = nw]

Idle(p) ==
    /\ pc[p] = "idle"
    /\ frontier = {}
    /\ UNCHANGED <<marked, frontier, pc, sel, succSet>>

Next ==
    \E p \in Procs : PickNode(p) \/ Expand(p) \/ Idle(p)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succSet>>

(*-----------------------------------------------------------------
  Invariant required by the configuration
-----------------------------------------------------------------*)
Inv ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A p \in Procs :
          /\ pc[p] \in {"idle","pick","expand"}
          /\ (pc[p] = "idle" => sel[p] = None)
          /\ (pc[p] = "expand" => sel[p] \in Nodes)
          /\ succSet[p] \subseteq Nodes

(*-----------------------------------------------------------------
  Property asserting refinement of the sequential Misra algorithm.
  For this configuration we state that the set of marked nodes is
  always a superset of the nodes that would be marked by the
  sequential algorithm (which is precisely the reachable set from
  Root using Succ).  This captures the intended refinement.
-----------------------------------------------------------------*)
Reachable ==
    RECURSIVE Reach(_,_)
    Reach(start, visited) ==
        IF start \in visited THEN visited
        ELSE LET new == \E n \in Succ[start] : n
                 visited' == visited \cup {start}
             IN UNION {Reach(n, visited') : n \in Succ[start]}

SeqMarked == Reach(Root, {})

Refines == SeqMarked \subseteq marked

====