---- MODULE Reachable ----
EXTENDS Sequences, TLC, FiniteSets, Naturals

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

(*-----------------------------------------------------------------
  Operators required by the configuration
-----------------------------------------------------------------*)
ConnectedToSomeButNotAll == Succ

LimitedSeq(S) == { s \in Seq(S) : Len(s) <= 5 }

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
(* Binary relation representing the graph edges *)
E(x, y) == y \in Succ[x]

(* Reachable nodes from a set of start nodes using transitive closure *)
Reach(S) == { y \in Nodes :
                \E x \in S : (x = y) \/ (x, y) \in TC(E) }

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"
    /\ TypeOK

Next ==
    \/ /\ pc = "run"
       /\ frontier # {}
       /\ \E n \in frontier :
            \/ /\ n \notin marked
               /\ marked' = marked \cup {n}
               /\ frontier' = frontier \cup Succ[n]
               /\ UNCHANGED pc
            \/ /\ n \in marked
               /\ frontier' = frontier \ {n}
               /\ UNCHANGED <<marked, pc>>
    \/ /\ pc = "run"
       /\ frontier = {}
       /\ pc' = "done"
       /\ UNCHANGED <<marked, frontier>>

Spec ==
    Init /\ [][Next]_<<marked, frontier, pc>> /\ WF_vars(Next)

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "done"}

Inv1 ==
    \A m \in marked : Succ[m] \subseteq marked \cup frontier

Inv2 ==
    marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 ==
    Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
    /\ pc = "done"
    => marked = Reach({Root})

(*-----------------------------------------------------------------
  Liveness property
-----------------------------------------------------------------*)
Termination ==
    <> (pc = "done")

=============================================================================