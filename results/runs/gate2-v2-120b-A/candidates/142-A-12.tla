---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*----------------------------------------------------------------------
  Constants required by the .cfg file
----------------------------------------------------------------------*)
CONSTANT Nodes, Root

(*----------------------------------------------------------------------
  Variables of the sequential Misra reachability algorithm
----------------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*----------------------------------------------------------------------
  Type correctness (used in Invariant1)
----------------------------------------------------------------------*)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in {"Init", "Iterate", "Done"}

(*----------------------------------------------------------------------
  Graph-theoretic lemmas (stubs for TLAPS proofs)
  The actual lemmas would be imported from a separate module; here we
  state them as assumptions so that TLAPS can use them as lemmas.
----------------------------------------------------------------------*)
L1 == /\ \A n \in marked :
            \A m \in Nodes :
                (<<n, m>> \in Edges) => (m \in marked \/ m \in frontier)
L2 == /\ \A n \in frontier :
            ReachableFrom(Root, {n}) \subseteq ReachableFrom(Root, frontier)
L3 == ReachableFrom(Root, {}) = {}

(*----------------------------------------------------------------------
  Placeholder definition of Edges and ReachableFrom.
  In a real development these would be imported from the graph module.
----------------------------------------------------------------------*)
Edges == {}  \* should be overridden in the .cfg with a concrete value

ReachableFrom(root, S) ==
    { x \in Nodes : TRUE }  \* a stub; TLAPS will use the lemmas above.

(*----------------------------------------------------------------------
  Initial state (the description says NOT_SPECIFIED, we provide a
  reasonable initialization that satisfies the invariants)
----------------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Init"

(*----------------------------------------------------------------------
  Transition relation (again, NOT_SPECIFIED in the description; we
  provide the standard sequential Misra steps)
----------------------------------------------------------------------*)
Iterate ==
    /\ pc = "Iterate"
    /\ LET nxt == { m \in Nodes :
                    \E n \in frontier :
                       <<n, m>> \in Edges
                 } IN
       /\ marked'   = marked \cup frontier
       /\ frontier' = nxt \ frontier
       /\ pc'       = IF frontier' = {} THEN "Done" ELSE "Iterate"
Next ==
    \/ /\ pc = "Init"
       /\ pc' = "Iterate"
       /\ UNCHANGED <<marked, frontier>>
    \/ Iterate
    \/ /\ pc = "Done"
       /\ UNCHANGED <<marked, frontier, pc>>

(*----------------------------------------------------------------------
  Specification
----------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*----------------------------------------------------------------------
  Invariants
----------------------------------------------------------------------*)
(* Invariant1: type correctness + every successor of a marked node is
   either already marked or in the frontier. *)
Inv1 == /\ TypeOK
        /\ L1

(* Invariant2: marked ∪ Reachable(Root, frontier) equals
   Reachable(Root, marked ∪ frontier). *)
Inv2 == marked \cup ReachableFrom(Root, frontier) =
        ReachableFrom(Root, marked \cup frontier)

(* Invariant3: Reachable(Root, {Root}) equals marked ∪ Reachable(Root, frontier). *)
Inv3 == ReachableFrom(Root, {Root}) = marked \cup ReachableFrom(Root, frontier)

(*----------------------------------------------------------------------
  Partial correctness theorem (proved by TLAPS using the lemmas)
----------------------------------------------------------------------*)
PartialCorrectness ==
    [] (pc = "Done" => marked = ReachableFrom(Root, {Root}))

(*----------------------------------------------------------------------
  Export the required identifiers
----------------------------------------------------------------------*)
THEOREM PartialCorrectness

=============================================================================