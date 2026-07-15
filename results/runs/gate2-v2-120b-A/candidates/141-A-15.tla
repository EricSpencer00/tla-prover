---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*--------------------------------------------------------------------
  Constants (to be supplied in the .cfg file)
--------------------------------------------------------------------*)
CONSTANTS Nodes, Root, Succ, Seq

(*--------------------------------------------------------------------
  Derived constants
--------------------------------------------------------------------*)
\* The set of all graph nodes
NodeSet == Nodes

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
\* The set of nodes reachable from a given set of nodes via the
\* successor relation (including the starting nodes themselves)
ReachableFrom(S) == 
    LET R == RECURSIVE R(_)
    IN R(S) = S \cup UNION { Succ[n] : n \in R(S) }

\* For readability
Marked == marked
Frontier == frontier
PC == pc

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Running"

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
\* Choose a node n from the current frontier
ChooseFrontierNode == 
    \E n \in frontier :
        /\ IF n \in marked
           THEN 
                /\ marked' = marked
                /\ frontier' = frontier \ {n}
                /\ pc' = "Running"
           ELSE 
                /\ marked' = marked \cup {n}
                /\ frontier' = frontier \cup Succ[n]
                /\ pc' = "Running"
        /\ UNCHANGED << >>

\* Termination action: when frontier is empty we move to the terminated state
Terminate ==
    /\ frontier = {}
    /\ pc' = "Terminated"
    /\ UNCHANGED << marked, frontier >>

\* Stuttering step to keep the model total
Stutter ==
    /\ pc = "Terminated"
    /\ UNCHANGED << marked, frontier, pc >>

Next ==
    \/ ChooseFrontierNode
    \/ Terminate
    \/ Stutter

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*--------------------------------------------------------------------
  Type correctness invariant
--------------------------------------------------------------------*)
TypeOK ==
    /\ marked \subseteq NodeSet
    /\ frontier \subseteq NodeSet
    /\ pc \in {"Running", "Terminated"}

(*--------------------------------------------------------------------
  Safety (partial correctness) invariants derived from the description
--------------------------------------------------------------------*)
\* Inv1: every successor of a marked node is either marked or in the frontier
Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* Inv2: the union of marked and the nodes reachable from frontier equals
\* the nodes reachable from the union of marked and frontier
Inv2 ==
    (marked \cup ReachableFrom(frontier)) =
    ReachableFrom(marked \cup frontier)

\* Inv3: the reachable set from Root equals marked union the reachable set from frontier
Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

\* PartialCorrectness: when terminated, marked equals the reachable set from Root
PartialCorrectness ==
    pc = "Terminated" => marked = ReachableFrom({Root})

(*--------------------------------------------------------------------
  Liveness property (termination when reachable set is finite)
--------------------------------------------------------------------*)
Termination ==
    WF_vars(Next)

(*--------------------------------------------------------------------
  THEOREMS (optional, for readability)
--------------------------------------------------------------------*)
THEOREM Spec => []TypeOK
THEOREM Spec => []Inv1
THEOREM Spec => []Inv2
THEOREM Spec => []Inv3
THEOREM Spec => []PartialCorrectness
THEOREM Spec => Termination

====