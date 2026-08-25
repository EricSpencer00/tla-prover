---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ

(*--------------------------------------------------------------------
  Operators required by the configuration
--------------------------------------------------------------------*)
ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq(S) == Seq(S)   \* a finite version of Seq (Seq is already finite)

(*--------------------------------------------------------------------
  Derived definitions
--------------------------------------------------------------------*)
SuccRel == { <<x, y>> : x \in Nodes /\ y \in Succ[x] }

Reach(S) == { n \in Nodes :
                \E m \in S : <<m, n>> \in TC(SuccRel) }

ReachRoot == Reach({Root})

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

(*--------------------------------------------------------------------
  Type correctness invariant
--------------------------------------------------------------------*)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Run", "Done"}

(*--------------------------------------------------------------------
  Initialization
--------------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"
    /\ TypeOK

(*--------------------------------------------------------------------
  Main action (the algorithm step)
--------------------------------------------------------------------*)
MainAction ==
    /\ pc = "Run"
    /\ \E n \in frontier :
         \/ /\ n \notin marked
                /\ marked' = marked \cup {n}
                /\ frontier' = frontier \cup Succ[n]
         \/ /\ n \in marked
                /\ frontier' = frontier \ {n}
                /\ marked' = marked
    /\ pc' = IF frontier' = {} THEN "Done" ELSE "Run"

Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<marked, frontier, pc>>

Next == MainAction \/ Stutter

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(*--------------------------------------------------------------------
  Safety invariants
--------------------------------------------------------------------*)
Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 == marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 == ReachRoot = marked \cup Reach(frontier)

PartialCorrectness == (pc = "Done") => (marked = ReachRoot)

(*--------------------------------------------------------------------
  Liveness property
--------------------------------------------------------------------*)
Termination == <> (pc = "Done")

====