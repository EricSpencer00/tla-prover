---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------------
  Constants (must match the cfg file)
-----------------------------------------------------------------------*)
CONSTANTS Nodes, Root

(*-----------------------------------------------------------------------
  Variables
-----------------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*-----------------------------------------------------------------------
  Derived definitions
-----------------------------------------------------------------------*)
Unmarked == Nodes \ marked

(*-----------------------------------------------------------------------
  Initial state
-----------------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Start"

(*-----------------------------------------------------------------------
  Actions
-----------------------------------------------------------------------*)
Next ==
    \/ /\ pc = "Start"
       /\ frontier # {}
       /\ \E n \in frontier :
            /\ marked'   = marked \cup {n}
            /\ frontier' = (frontier \ {n}) \cup { m \in Nodes : m \notin marked \cup frontier \land \E e \in Edges(n) : e = m }
            /\ pc' = "Start"
    \/ /\ pc = "Start"
       /\ frontier = {}
       /\ marked' = marked
       /\ frontier' = frontier
       /\ pc' = "Done"

(*-----------------------------------------------------------------------
  Specification
-----------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*-----------------------------------------------------------------------
  Invariants (as described)
-----------------------------------------------------------------------*)
Inv1 ==
    /\ \A n \in marked :
         \A m \in Edges(n) : m \in marked \/ m \in frontier
    /\ frontNext == { m \in Nodes : \E n \in marked : m \in Edges(n) }
    /\ frontier \subseteq Nodes \ marked

Inv2 ==
    marked \cup (ReachableFrom(frontier, Nodes)) =
    ReachableFrom(marked \cup frontier, Nodes)

Inv3 ==
    ReachableFrom({Root}, Nodes) =
    marked \cup (ReachableFrom(frontier, Nodes))

(*-----------------------------------------------------------------------
  Helper for reachability (graph-theoretic lemmas are assumed)
-----------------------------------------------------------------------*)
ReachableFrom(S, V) ==
    LET R == { n \in V :
                \E p \in Seq(V) :
                    Len(p) > 0 /\ p[1] \in S /\ p[Len(p)] = n /\
                    \A i \in 1..(Len(p)-1) : p[i+1] \in Edges(p[i]) }
    IN R

(*-----------------------------------------------------------------------
  Edges relation (must be defined for the model; can be overridden)
-----------------------------------------------------------------------*)
Edges(n) == {}

(*-----------------------------------------------------------------------
  Theorem (partial correctness) – not directly checked by TLC but
  required for TLAPS.
-----------------------------------------------------------------------*)
THEOREM TerminationImpliesCorrectness ==
    Spec => (pc = "Done") => (marked = ReachableFrom({Root}, Nodes))

====