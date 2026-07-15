---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, TLC

(*---------------------------------------------------------------------
  Constants
---------------------------------------------------------------------*)
CONSTANTS
    Nodes,   \* The set of all graph nodes
    Root,    \* The distinguished start node
    Edge     \* Edge must be a binary relation on Nodes (used by imports)

(*---------------------------------------------------------------------
  Variables
---------------------------------------------------------------------*)
VARIABLES
    marked,   \* Set of nodes that have been processed
    frontier, \* Set of nodes discovered but not yet processed
    pc        \* Program counter (identifies the current action)

(*---------------------------------------------------------------------
  Type correctness (used in Invariant1)
---------------------------------------------------------------------*)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in {"Init", "Process", "Done"}

(*---------------------------------------------------------------------
  Reachability functions (used in invariants)
---------------------------------------------------------------------*)
ReachableFrom[S \in SUBSET Nodes] ==
    UNION { ReachableFromNode[n] : n \in S }
    
ReachableFromNode[n \in Nodes] ==
    LET Rec(s) ==
        IF s = {}
            THEN {}
            ELSE
                LET x == CHOOSE y \in s : TRUE IN
                {x} \cup Rec({ y \in Nodes : <<x, y>> \in Edge } \ s)
    IN Rec({n})

(*---------------------------------------------------------------------
  Algorithm actions (abstractly described)
---------------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Init"

Process ==
    /\ pc = "Process"
    /\ frontier # {}
    /\ \E n \in frontier:
        /\ marked' = marked \cup {n}
        /\ frontier' = (frontier \ {n}) \cup
                       { m \in Nodes : <<n, m>> \in Edge } \ marked
        /\ pc' = "Process"
    /\ UNCHANGED pc

Done ==
    /\ pc = "Process"
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

Terminate ==
    /\ pc = "Done"
    /\ UNCHANGED <<marked, frontier, pc>>

Next ==
    \/ Init
    \/ Process
    \/ Done
    \/ Terminate

(*---------------------------------------------------------------------
  Specification
---------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*---------------------------------------------------------------------
  Invariants
---------------------------------------------------------------------*)
Invariant1 ==
    /\ TypeOK
    /\ \A n \in marked :
          \A m \in Nodes :
            <<n, m>> \in Edge => (m \in marked \/ m \in frontier)

Invariant2 ==
    /\ marked \cup ReachableFrom[frontier] =
       ReachableFrom[marked \cup frontier]

Invariant3 ==
    ReachableFrom[{Root}] = marked \cup ReachableFrom[frontier]

(*---------------------------------------------------------------------
  Safety property (the theorem to be checked)
---------------------------------------------------------------------*)
PartialCorrectness ==
    /\ pc = "Done"
    => marked = ReachableFrom[{Root}]

(*---------------------------------------------------------------------
  THEOREM (optional, can be checked with TLAPS)
---------------------------------------------------------------------*)
THEOREM Spec => []Invariant1 /\ []Invariant2 /\ []Invariant3 => []PartialCorrectness

====