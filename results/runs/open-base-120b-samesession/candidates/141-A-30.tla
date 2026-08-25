---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ

(*--------------------------------------------------------------------
  Operators substituted by the .cfg file
--------------------------------------------------------------------*)
ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq(S) == { s \in Seq(S) : Len(s) <= 5 }

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*--------------------------------------------------------------------
  Derived relations and helper definitions
--------------------------------------------------------------------*)
SuccRel == { <<x, y>> : x \in Nodes /\ y \in Succ[x] }

ReachFrom(S) == 
  S \cup { n \in Nodes : \E s \in S : <<s, n>> \in TC(SuccRel) }

Reachable == ReachFrom({Root})

(*--------------------------------------------------------------------
  Initial condition
--------------------------------------------------------------------*)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Running"

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
  \/ \E n \in frontier :
        /\ n \notin marked
        /\ marked'   = marked \cup {n}
        /\ frontier' = frontier \cup Succ[n]
        /\ pc'       = pc
  \/ \E n \in frontier :
        /\ n \in marked
        /\ marked'   = marked
        /\ frontier' = frontier \ {n}
        /\ pc'       = pc
  \/ /\ frontier = {}
        /\ pc'       = "Done"
        /\ UNCHANGED <<marked, frontier>>

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"Running", "Done"}

Inv1 ==
  \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
  marked \cup ReachFrom(frontier) = ReachFrom(marked \cup frontier)

Inv3 ==
  Reachable = marked \cup ReachFrom(frontier)

PartialCorrectness ==
  (pc = "Done") => (marked = Reachable)

(*--------------------------------------------------------------------
  Liveness property
--------------------------------------------------------------------*)
Termination == <> (pc = "Done")

=============================================================================