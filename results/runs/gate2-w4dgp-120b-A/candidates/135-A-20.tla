---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

\* A configuration module for the model-checking version of the
\* sequential Misra reachability algorithm.  It supplies concrete,
\* fully finite definitions for exactly the symbols the .cfg overrides
\* and the symbols it requires to be declared.  The reachability
\* algorithm itself builds on the standard reachability definition
\* (Inv1-Inv3, PartialCorrectness) plus the termination
\* property.  The graph here is fixed to 4 nodes with a deterministic
\* degree-2 successor relation; sequences are made finite so the
\* exhaustive model check terminates.

CONSTANTS Nodes, Root, Succ

\* "Seq" is overridden in the .cfg with LimitedSeq below.  It is not
\* re-declared here: EXTENDS Sequences brings Seq into scope and
\* LimitedSeq simply replaces its semantics via the .cfg substitution.
VARIABLES marked, frontier, pc

TypeOK == /\ marked \subseteq Nodes
          /\ frontier \subseteq Nodes
          /\ pc \in {0, 1, 2}

Init == /\ marked = {Root}
        /\ frontier = {Root}
        /\ pc = 0

Explore == /\ frontier # {}
          /\ frontier' = \bigcup_{n \in frontier} Succ[n]
          /\ marked' = marked \cup frontier'
          /\ frontier' \cap marked = {}
          /\ pc' = 1

Finish == /\ frontier = {}
          /\ frontier' = frontier
          /\ marked' = marked
          /\ pc' = 2

Next == Explore \/ Finish

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* Inv1 is the reachable-from-root closure: every marked node is
\* reachable by some (now-finite) sequence from the root.
Inv1 == \A n \in marked : \E seq \in LimitedSeq(Nodes) :
           /\ Len(seq) > 0
           /\ seq[1] = Root
           /\ seq[Len(seq)] = n
           /\ \A i \in 1..(Len(seq)-1) : seq[i+1] \in Succ[seq[i]]

Inv2 == \A n \in frontier : n \notin marked

Inv3 == \A n \in frontier :
           \A m \in frontier :
             (n # m) => (n \notin Succ[m] /\ m \notin Succ[n])

PartialCorrectness ==
  /\ \A n \in Nodes : (n \in marked) <=> ReachableFromRoot(n)
  /\ (Root \in marked)

Termination == <> (pc = 2)

====