---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, TLC

(*--------------------------------------------------------------------
  Constants required by the .cfg file
--------------------------------------------------------------------*)
CONSTANTS Nodes, Root

(*--------------------------------------------------------------------
  State variables inherited from the sequential reachability algorithm
--------------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*--------------------------------------------------------------------
  Type correctness (for completeness of the model)
--------------------------------------------------------------------*)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Init", "Loop", "Done"}

(*--------------------------------------------------------------------
  Derived definitions
--------------------------------------------------------------------*)
(* Successors of a node; this is a placeholder and should be
   refined to match the underlying graph definition. *)
Successors(n) == {}

ReachableFrom(S) ==
    LET Rec(s) ==
        s \cup { t \in Nodes : \E u \in s : t \in Successors(u) }
    IN  CHOOSE I \in Nat : Rec^[I](S) = Rec^[I+1](S)

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Init"

(*--------------------------------------------------------------------
  Actions (not fully specified in the description; we provide a
  generic loop that processes the frontier)
--------------------------------------------------------------------*)
DoStep ==
    /\ pc = "Loop"
    /\ frontier # {}
    /\ LET n == CHOOSE x \in frontier : TRUE
       IN /\ frontier' = (frontier \ {n}) \cup (Successors(n) \ marked)
          /\ marked'   = marked \cup {n}
    /\ pc' = IF frontier' = {} THEN "Done" ELSE "Loop"

Terminate ==
    /\ pc = "Loop"
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ pc = "Init"
       /\ pc' = "Loop"
       /\ UNCHANGED <<marked, frontier>>
    \/ DoStep
    \/ Terminate

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
Inv1 == 
    /\ TypeOK
    /\ \A m \in marked :
          \A s \in Successors(m) : s \in marked \/ s \in frontier

Inv2 == 
    (marked \cup ReachableFrom(frontier)) = ReachableFrom(marked \cup frontier)

Inv3 == 
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

(*--------------------------------------------------------------------
  Theorems (partial correctness)
--------------------------------------------------------------------*)
THEOREM PartialCorrectness ==
    Spec => [] (pc = "Done" => marked = ReachableFrom({Root}))

=================================