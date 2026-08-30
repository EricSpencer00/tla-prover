---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

\* Model-checking configuration for the sequential Misra reachability algorithm.
\* Overrides the infinite-sequence operator with a finite bounded version so
\* the state space stays finite, and instantiates a concrete 2-succ graph.

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"working", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "working"

Expand(n) ==
  /\ n \in frontier
  /\ frontier' = (frontier \setminus {n}) \cup Succ[n]
  /\ marked' = marked \cup Succ[n]
  /\ UNCHANGED pc

Complete ==
  /\ frontier = {}
  /\ pc = "working"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Idle ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ \E n \in Nodes : Expand(n)
  \/ Complete
  \/ Idle

Spec == Init /\ [][Next]_vars /\ WF_vars(Complete)

\* Successor closure: the frontier is always contained in the reachable set.
Inv1 == frontier \subseteq marked

\* Reachable nodes are exactly those reachable from the root via a real path.
Inv2 ==
  \A n \in Nodes :
    n \in marked <=>
      \E seq \in LimitedSeq(Nodes) :
        /\ seq # <<>>
        /\ Head(seq) = Root
        /\ Last(seq) = n
        /\ \A i \in DOMAIN seq : seq[i] \in Nodes
        /\ \A i \in 1 .. (Len(seq) - 1) : seq[i + 1] \in Succ[seq[i]]

\* Reachable nodes decompose into the initial node plus all of its successors.
Inv3 ==
  /\ Root \in marked
  /\ marked \subseteq {Root} \cup ConnectedToSomeButNotAll

\* The sequential algorithm's partial correctness: it never marks a node
\* that is not reachable from the root via a genuine path.
PartialCorrectness == Inv2

Termination == pc = "done"

====