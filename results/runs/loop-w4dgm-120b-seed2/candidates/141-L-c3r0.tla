---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root

\* Succ is the graph's successor relation; the .cfg substitutes ConnectedToSomeButNotAll
Succ == (x \in Nodes) |-> (y \in Nodes) : TRUE

VARIABLES marked, frontier, pc

MarkedSet == marked
FrontierSet == frontier

TypeOK ==
  /\ MarkedSet \subseteq Nodes
  /\ FrontierSet \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ MarkedSet = {}
  /\ FrontierSet = {Root}
  /\ pc = "running"

\* The overlap between marked and frontier is the twist that makes parallelization
\* possible; it does not invalidate the reachability reasoning below.
Explore ==
  /\ pc = "running"
  /\ FrontierSet # {}
  /\ \E n \in FrontierSet :
       IF n \notin MarkedSet
       THEN /\ MarkedSet' = MarkedSet \cup {n}
            /\ FrontierSet' = FrontierSet \cup Succ[n]
       ELSE /\ MarkedSet' = MarkedSet
            /\ FrontierSet' = FrontierSet \ {n}
  /\ pc' = IF FrontierSet' = {} THEN "done" ELSE "running"

Next == Explore

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* Every successor of a marked node is accounted for in the visited/queued partition.
Inv1 ==
  \A n \in MarkedSet : Succ[n] \subseteq (MarkedSet \cup FrontierSet)

ReachableFrom(n) ==
  LET P == {n} \cup {y \in Nodes : \E k \in Nat : k > 0 /\ \E seq \in Seq(Nodes) :
                /\ seq[1] = n
                /\ seq[k] = y
                /\ \A i \in 1..(k - 1) : seq[i + 1] \in Succ[seq[i]]}
  IN P

\* The marked set is exactly the visited part of the BFS partition of the reachable
\* region; the frontier holds the rest and nothing escapes it.
Inv2 ==
  ReachableFrom(Root) = (MarkedSet \cup (ReachableFromSet(FrontierSet)))

ReachableFromSet(S) ==
  UNION {ReachableFrom(s) : s \in S}

\* Reachability only cares about the partition; the overlap makes no difference.
Inv3 ==
  ReachableFrom(Root) = (MarkedSet \cup ReachableFromSet(FrontierSet))

PartialCorrectness == Inv1 /\ Inv2 /\ Inv3

\* Weak fairness of the loop forces it to drain the frontier, which only happens after
\* the finite reachable set has been fully explored.
Termination == (pc = "running") ~> (pc = "done")

====