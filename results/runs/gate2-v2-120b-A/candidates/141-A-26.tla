---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

(*--------------------------------------------------------------------
  Constants (to be instantiated in the .cfg file)
--------------------------------------------------------------------*)
CONSTANTS Nodes, Root, Succ, Seq

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
Node == Nodes

Roots == {Root}

(* The set of all nodes that are reachable from a given set of start nodes *)
ReachableFrom(start) == 
    LET rec(_) == 
        UNION { Succ[n] : n \in start } \cup start
    IN 
        FixedPoint(rec, start)

(* Fixed point computation (iterative until a fixpoint is reached) *)
FixedPoint(f, init) ==
    LET iter(k) == IF k = 0 THEN init ELSE iter(k-1) \cup f(iter(k-1))
    IN  CHOOSE n \in Nat : iter(n) = iter(n+1)

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES marked, frontier, pc

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
MarkOrAdd ==
    \E n \in frontier :
        IF n \notin marked THEN
            /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
        ELSE
            /\ marked' = marked
            /\ frontier' = frontier \ {n}
        /\ UNCHANGED pc

Terminate ==
    /\ frontier = {}
    /\ pc = "Running"
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ MarkOrAdd
    \/ Terminate

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
    /\ pc \in {"Running", "Done"}

(*--------------------------------------------------------------------
  Safety invariants described in the natural-language text
--------------------------------------------------------------------*)
Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
    \A F \in SUBSET Nodes :
        ReachableFrom(marked \cup F) = marked \cup ReachableFrom(F)

Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness ==
    /\ pc = "Done"
    /\ frontier = {}
    /\ marked = ReachableFrom({Root})

(*--------------------------------------------------------------------
  Liveness (termination) property
--------------------------------------------------------------------*)
Termination == <> (pc = "Done")

=============================================================================