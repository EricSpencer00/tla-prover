---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Constants required by the configuration
\* ----------------------------------------------------------------------
CONSTANTS Nodes, Root, Succ

\* Concrete graph definition (4 nodes, each with exactly 2 successors)
Nodes == {1, 2, 3, 4}
Root  == 1
Succ  == [ 1 |-> {2, 3},
          2 |-> {3, 4},
          3 |-> {1, 4},
          4 |-> {1, 2} ]

\* ----------------------------------------------------------------------
\* Operator that will be substituted for Succ in the algorithm
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

\* ----------------------------------------------------------------------
\* Bounded sequence operator (replaces Seq from Sequences)
\* ----------------------------------------------------------------------
LimitedSeq == { s \in Seq : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\* State variables (inherited from the sequential reachability algorithm)
\* ----------------------------------------------------------------------
VARIABLES Marked, Frontier, pc

\* ----------------------------------------------------------------------
\* Type‑correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ pc \in {"Run", "Done"}

\* ----------------------------------------------------------------------
\* Initial state (inherited)
\* ----------------------------------------------------------------------
Init ==
    /\ Marked = {}
    /\ Frontier = {Root}
    /\ pc = "Run"

\* ----------------------------------------------------------------------
\* Next‑state relation (inherited, unchanged)
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pc = "Run"
       /\ \E n \in Frontier:
            /\ Marked'   = Marked \cup {n}
            /\ Frontier' = (Frontier \ {n}) \cup (ConnectedToSomeButNotAll(n) \ Marked)
            /\ pc'       = "Run"
    \/ /\ pc = "Run"
       /\ Frontier = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<Marked, Frontier>>

\* ----------------------------------------------------------------------
\* Specification formula required by the .cfg file
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

\* ----------------------------------------------------------------------
\* Algorithm invariants required by the .cfg file
\* ----------------------------------------------------------------------
Inv1 == \A n \in Marked :
          ConnectedToSomeButNotAll(n) \subseteq Marked \/ Frontier

Inv2 == \A n \in Nodes :
          (n \in Marked) => (n = Root) \/ (\E m \in Marked : n \in ConnectedToSomeButNotAll(m))

Inv3 == (Marked = Nodes) => (Frontier = {})

PartialCorrectness == (pc = "Done") => (Marked = Nodes)

\* ----------------------------------------------------------------------
\* Liveness property required by the .cfg file
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

====