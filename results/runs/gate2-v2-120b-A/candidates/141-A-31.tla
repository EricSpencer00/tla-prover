---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

(*--------------------------------------------------------------------
  Constants (must be defined in the .cfg file)
--------------------------------------------------------------------*)
CONSTANTS Nodes, Root, Succ, Seq

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
(* The set of all nodes reachable from a given set of start nodes,
   following the successor relation Succ. This is the least fixed point
   of the successor expansion. *)
ReachableFrom(S) ==
  LET R == { n \in Nodes : \E m \in S : n \in Succ[m] } UNION S IN
    IF R = S THEN S ELSE ReachableFrom(R)

(* The set of nodes reachable from the designated root, used in invariants. *)
RootReachable == ReachableFrom({Root})

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Run"

(*--------------------------------------------------------------------
  Main action
--------------------------------------------------------------------*)
RemoveOrAdd ==
  \E x \in frontier :
    IF x \in marked THEN
      /\ marked' = marked
      /\ frontier' = frontier \ {x}
    ELSE
      /\ marked' = marked \cup {x}
      /\ frontier' = frontier \cup Succ[x]

Terminate ==
  /\ frontier = {}
  /\ marked' = marked
  /\ frontier' = frontier
  /\ pc' = "Done"

Next ==
  \/ /\ pc = "Run"
        /\ (RemoveOrAdd \/ Terminate)
  \/ /\ pc = "Done"
        /\ UNCHANGED <<marked, frontier, pc>>

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*--------------------------------------------------------------------
  Type correctness invariant
--------------------------------------------------------------------*)
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"Run", "Done"}

(*--------------------------------------------------------------------
  Safety invariants (the three core invariants described)
--------------------------------------------------------------------*)
(* Inv1: every successor of a marked node is either marked or in frontier *)
Inv1 ==
  \A n \in marked : Succ[n] \subseteq marked \cup frontier

(* Inv2: the union of marked and the nodes reachable from frontier
         equals the nodes reachable from the union of marked and frontier *)
Inv2 ==
  ReachableFrom(marked \cup frontier) = marked \cup ReachableFrom(frontier)

(* Inv3: the set of nodes reachable from the root equals marked plus
         the nodes reachable from frontier *)
Inv3 ==
  RootReachable = marked \cup ReachableFrom(frontier)

(* Partial correctness: when terminated, marked equals the reachable set *)
PartialCorrectness ==
  /\ pc = "Done"
  /\ frontier = {}
  => marked = RootReachable

(*--------------------------------------------------------------------
  Liveness property (termination under weak fairness)
--------------------------------------------------------------------*)
Termination ==
  WF_vars(Next)

(* Declare the set of variables for WF operator *)
vars == <<marked, frontier, pc>>

====