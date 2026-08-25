---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANTS Nodes, Root, Succ

(*-----------------------------------------------------------------
  Operator that will be substituted for Succ in the configuration.
  It simply returns the successors given by the constant Succ.
-----------------------------------------------------------------*)
ConnectedToSomeButNotAll(n) == Succ[n]

(*-----------------------------------------------------------------
  A finite version of Seq, bounded by MaxSeqLen (also a constant).
-----------------------------------------------------------------*)
CONSTANT MaxSeqLen
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
\* Relation representation of the successor function
SuccRel == { <<n, m>> : n \in Nodes /\ m \in Succ[n] }

\* Nodes reachable from a set of start nodes (including the starts)
Reach(S) == S \cup { n \in Nodes : \E m \in S : <<m, n>> \in TC(SuccRel) }

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"

(*-----------------------------------------------------------------
  Main action (pick a node from the frontier)
-----------------------------------------------------------------*)
ChooseNode ==
    \E n \in frontier :
        /\ IF n \notin marked THEN
               /\ marked' = marked \cup {n}
               /\ frontier' = frontier \cup Succ[n]
           ELSE
               /\ marked' = marked
               /\ frontier' = frontier \ {n}
           ENDIF
        /\ pc' = pc

(*-----------------------------------------------------------------
  Termination action
-----------------------------------------------------------------*)
Terminate ==
    /\ frontier = {}
    /\ pc = "Run"
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ ChooseNode
    \/ Terminate

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec ==
    Init /\ [][Next]_<<marked, frontier, pc>> /\ WF_<<marked, frontier, pc>>(Next)

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Run", "Done"}

Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
    marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 ==
    Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
    /\ pc = "Done"
    /\ marked = Reach({Root})

(*-----------------------------------------------------------------
  Liveness property
-----------------------------------------------------------------*)
Termination == <> (pc = "Done")

(*-----------------------------------------------------------------
  The set of invariants and properties required by the .cfg file
-----------------------------------------------------------------*)
INVARS == TypeOK /\ Inv1 /\ Inv2 /\ Inv3 /\ PartialCorrectness

====