---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

\* Concrete graph definition (4 nodes, each with exactly 2 successors)
\* (The actual values of Nodes and Root are supplied by the .cfg file.)

\* ConnectedToSomeButNotAll is the finite successor relation used to
\* replace the original (unbounded) Succ operator.  It is a constant set
\* of ordered pairs, i.e., a binary relation.
ConnectedToSomeButNotAll ==
  { <<1, 2>>, <<1, 3>>,
    <<2, 3>>, <<2, 4>>,
    <<3, 1>>, <<3, 4>>,
    <<4, 1>>, <<4, 2>> }

\* Helper that extracts the set of successors of a node from the relation.
SuccSet(n) ==
  { m \in Nodes : <<n, m>> \in ConnectedToSomeButNotAll }

\* LimitedSeq replaces the unbounded Seq operator.
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* Helper for nondeterministic choice from a non‑empty set.
Choose(S) ==
  CHOOSE x \in S : TRUE

\* Reachable set defined using bounded sequences.
ReachableSet ==
  { n \in Nodes :
      \E s \in LimitedSeq(Nodes) :
        /\ Len(s) > 0
        /\ s[1] = Root
        /\ s[Len(s)] = n
        /\ \A i \in 1 .. Len(s)-1 :
            s[i+1] \in SuccSet(s[i])
  }

VARIABLES marked, frontier, pc

\* Initial state
Init ==
  /\ marked   = {Root}
  /\ frontier = SuccSet(Root)
  /\ pc       = "init"

\* One step of the sequential reachability algorithm
Next ==
  \/ /\ pc = "init"
     /\ pc' = "step"
     /\ UNCHANGED <<marked, frontier>>
  \/ /\ pc = "step"
     /\ frontier # {}
     /\ LET n == Choose(frontier) IN
          /\ marked'   = marked \cup {n}
          /\ frontier' = (frontier \ {n})
                         \cup (SuccSet(n) \ marked)
          /\ pc'       = "step"
  \/ /\ pc = "step"
     /\ frontier = {}
     /\ pc' = "done"
     /\ UNCHANGED <<marked, frontier>>

\* Specification required by the .cfg file
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* Type correctness invariant
TypeOK ==
  /\ marked   \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "step", "done"}

\* Invariant 1: successor closure
Inv1 ==
  \A n \in marked :
    SuccSet(n) \subseteq marked \cup frontier

\* Invariant 2: frontier contains only unmarked nodes
Inv2 ==
  \A n \in frontier : n \notin marked

\* Invariant 3: marked set equals the reachable set
Inv3 ==
  marked = ReachableSet

\* Partial correctness: when finished, marked equals the reachable set
PartialCorrectness ==
  pc = "done" => marked = ReachableSet

\* Liveness property: termination
Termination == <> (pc = "done")

====