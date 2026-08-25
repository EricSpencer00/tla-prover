---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
(* The successor relation used by the algorithm.  The .cfg substitutes
   ConnectedToSomeButNotAll for Succ, so we expose it as an operator. *)
ConnectedToSomeButNotAll == Succ

(* Finite version of Seq for model checking. *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= 5 }

(* Binary relation derived from the successor operator. *)
Rel == { <<n,m>> : n \in Nodes /\ m \in ConnectedToSomeButNotAll[n] }

(* Nodes reachable (by zero or more steps) from a set of nodes. *)
ReachableFrom(S) == 
  { m \in Nodes : 
      \E n \in S : 
        (<<n,m>> \in TC(Rel)) \/ n = m }

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "run"
  /\ Root \in Nodes

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
ActionNotMarked ==
  /\ pc = "run"
  /\ \E n \in frontier :
        /\ n \notin marked
        /\ marked' = marked \cup {n}
        /\ frontier' = frontier \cup ConnectedToSomeButNotAll[n]
        /\ pc' = IF frontier' = {} THEN "term" ELSE "run"

ActionMarked ==
  /\ pc = "run"
  /\ \E n \in frontier :
        /\ n \in marked
        /\ marked' = marked
        /\ frontier' = frontier \ {n}
        /\ pc' = IF frontier' = {} THEN "term" ELSE "run"

ActionTerminated ==
  /\ pc = "term"
  /\ UNCHANGED <<marked, frontier, pc>>

Next == ActionNotMarked \/ ActionMarked \/ ActionTerminated

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<marked, frontier, pc>>
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK == 
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes

Inv1 == \A n \in marked : ConnectedToSomeButNotAll[n] \subseteq marked \cup frontier

Inv2 == marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Inv3 == ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness == 
  /\ pc = "term"
  => marked = ReachableFrom({Root})

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Termination == <> (pc = "term")

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* (they are already named exactly as required)
====