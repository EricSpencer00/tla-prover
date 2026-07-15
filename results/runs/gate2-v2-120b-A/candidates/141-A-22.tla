---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

VARIABLES marked, frontier, pc

(*--------------------------------------------------------------------
  Constants (to be supplied in the .cfg file)
--------------------------------------------------------------------*)
CONSTANTS Nodes, Root, Succ, Seq

(*--------------------------------------------------------------------
  State predicates
--------------------------------------------------------------------*)
TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in {"Running", "Done"}

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
ReachableFrom(S) ==
  IF S = {} THEN {}
  ELSE
    LET
      step == { y \in Nodes : \E x \in S : y \in Succ[x] }
    IN
      IF step \subseteq S
      THEN S
      ELSE ReachableFrom(S \cup step)

AllReachable == ReachableFrom({Root})

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Running"
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ Root \in Nodes

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
Explore ==
  \E n \in frontier :
    IF n \notin marked THEN
      /\ marked' = marked \cup {n}
      /\ frontier' = frontier \cup Succ[n]
    ELSE
      /\ marked' = marked
      /\ frontier' = frontier \ {n}
    /\ pc' = "Running"

Terminate ==
  /\ frontier = {}
  /\ pc = "Done"
  /\ UNCHANGED <<marked, frontier, pc>>

Next ==
  \/ /\ pc = "Running"
        /\ frontier # {}
        /\ Explore
  \/ Terminate

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*--------------------------------------------------------------------
  Safety invariants
--------------------------------------------------------------------*)
Inv1 ==
  \A x \in marked :
    \A y \in Succ[x] :
      y \in marked \/ y \in frontier

Inv2 ==
  (marked \cup frontier) = ReachableFrom(marked \cup frontier)

Inv3 ==
  AllReachable = marked \cup ReachableFrom(frontier)

PartialCorrectness ==
  (frontier = {} /\ pc = "Done") => (marked = AllReachable)

(*--------------------------------------------------------------------
  Liveness property (termination)
--------------------------------------------------------------------*)
Termination ==
  WF_vars(Explore) /\ []<>(frontier = {})

====