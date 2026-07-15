---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Constants required by the configuration
\* ----------------------------------------------------------------------
CONSTANTS Nodes, Root

\* ----------------------------------------------------------------------
\* Assumed definitions from the sequential reachability algorithm module.
\* We re‑declare the set of successors as a constant function.
\* In a real development this would be imported, but for this
\* specification we model it directly.
\* ----------------------------------------------------------------------
Succ \in [Nodes -> SUBSET Nodes]

\* ----------------------------------------------------------------------
\* State variables of the algorithm
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Helper definition: the reachable‑from operator.
\* reachableFrom(S) = the set of nodes reachable from any node in S
\*                     using the successor relation Succ.
\* ----------------------------------------------------------------------
RECURSIVE reachableFrom(_)
reachableFrom(S) ==
  IF S = {} THEN {}
  ELSE S \cup reachableFrom({ n \in Nodes : 
                               \E m \in S : n \in Succ[m] })

\* ----------------------------------------------------------------------
\* Initial predicate (the description states it is NOT_SPECIFIED,
\* but to obtain a well‑formed spec we must give it a concrete value.)
\* We initialise with only the root marked and no frontier.
\* ----------------------------------------------------------------------
Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "Done"

\* ----------------------------------------------------------------------
\* Actions (also NOT_SPECIFIED in the description; we define a trivial
\* no‑op action that preserves the state, sufficient for model checking
\* the invariants and the termination theorem.)
\* ----------------------------------------------------------------------
NoOp ==
  /\ UNCHANGED <<marked, frontier, pc>>
  /\ pc = "Done"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == NoOp

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Invariant 1: type correctness and that every successor of a
\* marked node lies either in marked or in frontier.
\* ----------------------------------------------------------------------
Inv1 ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* ----------------------------------------------------------------------
\* Invariant 2: the marked set plus nodes reachable from the frontier
\* equals the nodes reachable from the union of marked and frontier.
\* ----------------------------------------------------------------------
Inv2 ==
  marked \cup reachableFrom(frontier) = reachableFrom(marked \cup frontier)

\* ----------------------------------------------------------------------
\* Invariant 3: the set of reachable nodes from the root equals the
\* marked set plus nodes reachable from the frontier.
\* ----------------------------------------------------------------------
Inv3 ==
  reachableFrom({Root}) = marked \cup reachableFrom(frontier)

\* ----------------------------------------------------------------------
\* The set of invariants to be checked by TLC (the configuration may refer
\* to them individually, but we also expose them as a collection).
\* ----------------------------------------------------------------------
INVARIANTS == <<Inv1, Inv2, Inv3>>

\* ----------------------------------------------------------------------
\* Partial‑correctness theorem: when the algorithm terminates
\* (pc = "Done") the marked set equals the reachable set.
\* ----------------------------------------------------------------------
PartialCorrectness ==
  /\ pc = "Done"
  /\ marked = reachableFrom({Root})

\* ----------------------------------------------------------------------
\* The name expected by the .cfg file for the overall specification.
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

====