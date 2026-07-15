---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Constants (to be supplied in the .cfg file)
-----------------------------------------------------------------*)
CONSTANTS
    Nodes,   \* The set of all graph nodes
    Root,    \* The distinguished start node
    Succ,    \* A function Succ \in [Nodes -> SUBSET Nodes] giving successors
    Seq      \* The set of states that the program counter can take

(*-----------------------------------------------------------------
  Derived sets and helper definitions
-----------------------------------------------------------------*)
ReachableFrom(S) == 
    \* Nodes reachable from any node in S via zero or more Succ steps
    LET R == UNION { RECURSIVE ReachNode(v) == {v} \cup UNION { ReachNode(w) : w \in Succ[v] } }
    IN  UNION { R[v] : v \in S }

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES
    marked,    \* Set of visited nodes
    frontier, \* Set of nodes pending exploration (may overlap with marked)
    pc         \* Program counter: "Run" or "Done"

(*-----------------------------------------------------------------
  Type correctness invariant
-----------------------------------------------------------------*)
TypeOK == 
    /\ marked    \in SUBSET Nodes
    /\ frontier  \in SUBSET Nodes
    /\ pc        \in {"Run", "Done"}

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ marked   = {}
    /\ frontier = {Root}
    /\ pc       = "Run"
    /\ TypeOK   \* Ensure the initial state respects the type invariant

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
PickUnmarked == 
    \E n \in frontier :
        /\ n \notin marked
        /\ marked'   = marked \cup {n}
        /\ frontier' = frontier \cup Succ[n]
        /\ pc'       = pc
        /\ UNCHANGED << >>

PickMarked == 
    \E n \in frontier :
        /\ n \in marked
        /\ marked'   = marked
        /\ frontier' = frontier \ {n}
        /\ pc'       = pc
        /\ UNCHANGED << >>

Terminate == 
    /\ frontier = {}
    /\ pc = "Done"
    /\ UNCHANGED <<marked, frontier, pc>>

Next == 
    \/ /\ pc = "Run"
       /\ frontier # {}
       /\ (PickUnmarked \/ PickMarked)
    \/ Terminate

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Safety invariants described in the natural-language text
-----------------------------------------------------------------*)
Inv1 == 
    \A n \in marked :
        Succ[n] \subseteq marked \cup frontier

Inv2 == 
    \A S \in SUBSET Nodes :
        ReachableFrom(marked \cup frontier) = 
            marked \cup ReachableFrom(frontier)

Inv3 == 
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness == 
    /\ pc = "Done"
    /\ marked = ReachableFrom({Root})

(*-----------------------------------------------------------------
  Liveness property (weak fairness ensures eventual termination for
  finite reachable sets)
-----------------------------------------------------------------*)
Termination == [](<> (pc = "Done"))

=============================================================================