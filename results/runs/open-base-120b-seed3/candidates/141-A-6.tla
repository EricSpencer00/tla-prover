---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

\*-----------------------------------------------------------------
\* Constants describing the graph
\*-----------------------------------------------------------------
CONSTANTS Nodes, Root, Succ

\*-----------------------------------------------------------------
\* Operator that will be substituted for Succ in the .cfg file.
\* It simply returns the successors of a node as defined by Succ.
\*-----------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

\*-----------------------------------------------------------------
\* A finite‑length version of Seq (the standard sequence operator).
\* Here we define it as just Seq, which already denotes the set of
\* all finite sequences over a set.
\*-----------------------------------------------------------------
LimitedSeq(S) == Seq(S)

\*-----------------------------------------------------------------
\* State variables
\*-----------------------------------------------------------------
VARIABLES marked, frontier, pc

\*-----------------------------------------------------------------
\* Helper recursive definition of the set of nodes reachable from a
\* set of source nodes using the successor relation Succ.
\*-----------------------------------------------------------------
RECURSIVE Reach(_)

Reach(S) == 
  IF S = {} THEN {} 
  ELSE S \cup Reach({ n \in Nodes : \E m \in S : n \in Succ[m] })

\*-----------------------------------------------------------------
\* Initial state
\*-----------------------------------------------------------------
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "run"
  /\ TypeOK

\*-----------------------------------------------------------------
\* Type correctness invariant (also used in Init)
\*-----------------------------------------------------------------
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ Root \in Nodes

\*-----------------------------------------------------------------
\* Main step: pick a node from the frontier and act
\*-----------------------------------------------------------------
PickNode ==
  \E n \in frontier :
    /\ IF n #\in marked THEN
         /\ marked' = marked \cup {n}
         /\ frontier' = frontier \cup ConnectedToSomeButNotAll(n)
       ELSE
         /\ marked' = marked
         /\ frontier' = frontier \ {n}
    /\ UNCHANGED pc

\*-----------------------------------------------------------------
\* Termination step: when the frontier is empty we move to the
\* terminated state.
\*-----------------------------------------------------------------
Terminate ==
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ PickNode
  \/ Terminate

\*-----------------------------------------------------------------
\* Specification
\*-----------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\*-----------------------------------------------------------------
\* Invariants
\*-----------------------------------------------------------------
Inv1 ==
  \A m \in marked : ConnectedToSomeButNotAll(m) \subseteq marked \cup frontier

Inv2 ==
  marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 ==
  Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
  /\ frontier = {}
  => marked = Reach({Root})

\*-----------------------------------------------------------------
\* Liveness property (termination)
\*-----------------------------------------------------------------
Termination == <> (frontier = {})

\*-----------------------------------------------------------------
\* The set of invariants for the model checker
\*-----------------------------------------------------------------
INVARIANTS == TypeOK /\ Inv1 /\ Inv2 /\ Inv3 /\ PartialCorrectness

====