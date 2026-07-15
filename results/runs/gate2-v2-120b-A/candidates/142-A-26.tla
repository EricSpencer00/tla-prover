---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Sequences

\*-----------------------------------------------------------------
-- Constants (declared in the .cfg file)
-----------------------------------------------------------------*/
CONSTANTS Nodes, Root

\*-----------------------------------------------------------------
-- State variables inherited from the sequential reachability algorithm
-----------------------------------------------------------------*/
VARIABLES marked, frontier, pc

\*-----------------------------------------------------------------
-- Helper definitions
-----------------------------------------------------------------*/
MarkedSet == marked
FrontierSet == frontier

\* The set of all nodes reachable from a given set via edges.
ReachableFrom(S) == 
  RECURSIVE RSet(_)
  RSet(s) == 
    IF s = {} THEN {} 
    ELSE LET n == CHOOSE x \in s : TRUE IN 
         s \cup (RSet({ y \in Nodes : (n, y) \in Edges }) \ { n })
  IN RSet(S)

\* The set of all nodes reachable from the root
Reachable == ReachableFrom({Root})

\*-----------------------------------------------------------------
-- Initial predicate (type correctness)
-----------------------------------------------------------------*/
Init == 
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "F"
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes

\*-----------------------------------------------------------------
-- Actions
-----------------------------------------------------------------*/
Mark == 
  /\ pc = "F"
  /\ \E n \in frontier :
        /\ frontier' = frontier \ {n}
        /\ marked'   = marked \cup {n}
        /\ pc' = IF frontier' = {} THEN "T" ELSE "F"
  /\ UNCHANGED << >>

Terminate == 
  /\ pc = "F"
  /\ frontier = {}
  /\ pc' = "T"
  /\ UNCHANGED << marked, frontier >>

\*-----------------------------------------------------------------
-- Next-state relation
-----------------------------------------------------------------*/
Next == 
  \/ Mark
  \/ Terminate

\*-----------------------------------------------------------------
-- Specification
-----------------------------------------------------------------*/
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\*-----------------------------------------------------------------
-- Invariant 1: type correctness plus every successor of a marked node
--                is in the marked set or frontier.
-----------------------------------------------------------------*/
Inv1 == 
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ \A n \in marked : 
        \A m \in Nodes : (n, m) \in Edges => (m \in marked \/ m \in frontier)

\*-----------------------------------------------------------------
-- Lemma 1 (graph‑theoretic, used to prove Inv2)
-----------------------------------------------------------------*/
Lemma1 == 
  \A S \subseteq Nodes :
    ReachableFrom(S) = S \cup ReachableFrom({ m \in Nodes : \E n \in S : (n, m) \in Edges })

\*-----------------------------------------------------------------
-- Invariant 2: marked ∪ reachable(frontier) = reachable(marked ∪ frontier)
-----------------------------------------------------------------*/
Inv2 == 
  ReachableFrom(marked \cup frontier) = marked \cup ReachableFrom(frontier)

\*-----------------------------------------------------------------
-- Lemma 2 (reachable‑from is stable under adding successors)
-----------------------------------------------------------------*/
Lemma2 == 
  \A S \subseteq Nodes, n \in Nodes :
    (ReachableFrom(S) \cup {n}) \subseteq ReachableFrom(S \cup {n})

\*-----------------------------------------------------------------
-- Lemma 3 (reachable from empty set is empty)
-----------------------------------------------------------------*/
Lemma3 == ReachableFrom({}) = {}

\*-----------------------------------------------------------------
-- Invariant 3: reachable(root) = marked ∪ reachable(frontier)
-----------------------------------------------------------------*/
Inv3 == 
  Reachable = marked \cup ReachableFrom(frontier)

\*-----------------------------------------------------------------
-- Final theorem (partial correctness)
-----------------------------------------------------------------*/
Termination == 
  pc = "T" => marked = Reachable

\*-----------------------------------------------------------------
-- The set of invariants required by the .cfg file
-----------------------------------------------------------------*/
INVARIANTS == Inv1 /\ Inv2 /\ Inv3

\*-----------------------------------------------------------------
-- The set of properties to be checked (here we expose the theorem)
-----------------------------------------------------------------*/
PROPERTIES == Termination

=============================================================================