---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Vars == << marked, frontier, pc >>

SuccRel == { <<x, y>> : x \in Nodes /\ y \in Succ[x] }

Reach(S) ==
  (* nodes reachable from any node in S via zero or more Succ steps *)
  S \cup { n \in Nodes :
            \E s \in S : <<s, n>> \in TC(SuccRel, S) }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Run"
  /\ Root \in Nodes

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "Run"
     /\ frontier # {}
     /\ \E n \in frontier :
          /\ IF n \notin marked
               THEN /\ marked'   = marked \cup {n}
                    /\ frontier' = frontier \cup Succ[n]
               ELSE /\ marked'   = marked
                    /\ frontier' = frontier \ {n}
          /\ pc' = IF frontier' = {} THEN "Done" ELSE "Run"
  \/ /\ pc = "Done"
     /\ UNCHANGED << marked, frontier, pc >>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_Vars /\ WF_Vars(Next)

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"Run", "Done"}

Inv1 ==
  \A m \in marked : Succ[m] \subseteq marked \cup frontier

Inv2 ==
  marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 ==
  Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
  (frontier = {}) => (marked = Reach({Root}))

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Termination == <> (frontier = {})

\* ----------------------------------------------------------------------
\* Operators required by the .cfg substitutions
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq(S) == { s \in Seq(S) : Len(s) <= 5 }

====