---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)

SuccRel == { <<n, m>> : n \in Nodes /\ m \in Succ[n] }

RECURSIVE ReachFrom(_)
ReachFrom(S) ==
    { m \in Nodes : \E n \in S : <<n, m>> \in TC(SuccRel) }

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"
    /\ Root \in Nodes

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)

PickNode ==
    \E n \in frontier :
        /\ IF n \notin marked
              THEN /\ marked'   = marked \cup {n}
                   /\ frontier' = frontier \cup Succ[n]
              ELSE /\ marked'   = marked
                   /\ frontier' = frontier \ {n}
        /\ UNCHANGED pc

Terminate ==
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

Next == PickNode \/ Terminate

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Run", "Done"}

Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
    (marked \cup ReachFrom(frontier)) = ReachFrom(marked \cup frontier)

Inv3 ==
    ReachFrom({Root}) = marked \cup ReachFrom(frontier)

PartialCorrectness ==
    (pc = "Done") => (marked = ReachFrom({Root}))

(*--------------------------------------------------------------------
  Liveness property
--------------------------------------------------------------------*)

Termination == <> (pc = "Done")

(*--------------------------------------------------------------------
  Operators required by the .cfg file
--------------------------------------------------------------------*)

ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq(S) == { s \in Seq(S) : Len(s) <= 5 }

=============================================================================