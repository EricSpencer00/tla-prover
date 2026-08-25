---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES Marked, Frontier, pc

(*-----------------------------------------------------------------
  Concrete graph: each node has exactly two successors.
  The .cfg substitutes Succ with ConnectedToSomeButNotAll.
-----------------------------------------------------------------*)
ConnectedToSomeButNotAll(n) ==
  { (n % 4) + 1 , ((n + 1) % 4) + 1 }  \* assumes Nodes = 1..4

(*-----------------------------------------------------------------
  Finite version of Seq, bounded by the number of nodes.
-----------------------------------------------------------------*)
MaxLen == Cardinality(Nodes)

LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= MaxLen }

(*-----------------------------------------------------------------
  Helper: a node is reachable from Root via a bounded path.
-----------------------------------------------------------------*)
Path(n) ==
  \E s \in LimitedSeq(Nodes) :
    /\ Len(s) > 0
    /\ s[1] = Root
    /\ s[Len(s)] = n
    /\ \A i \in 1..(Len(s) - 1) : s[i+1] \in ConnectedToSomeButNotAll[s[i]]

(*-----------------------------------------------------------------
  Initialization and next-state relation (inherited from the
  sequential reachability algorithm, expressed concretely here).
-----------------------------------------------------------------*)
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "start"

Next ==
  \/ /\ pc = "start"
     /\ pc' = "run"
     /\ UNCHANGED <<Marked, Frontier>>
  \/ /\ pc = "run"
     /\ \E n \in Frontier :
          /\ Marked' = Marked \cup {n}
          /\ Frontier' = (Frontier \ {n}) \cup ConnectedToSomeButNotAll[n]
          /\ pc' = "run"
          /\ UNCHANGED pc
  \/ /\ pc = "run"
     /\ Frontier = {}
     /\ pc' = "done"
     /\ UNCHANGED <<Marked, Frontier>>

Spec ==
  Init /\ [][Next]_<<Marked, Frontier, pc>>

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"start", "run", "done"}

Inv1 ==   \* successor closure
  \A n \in Marked : ConnectedToSomeButNotAll[n] \subseteq Marked \cup Frontier

Inv2 ==   \* every node in the explored frontier is reachable
  \A n \in Marked \cup Frontier : Path(n)

Inv3 ==   \* explored set equals the set of reachable nodes
  \A n \in Nodes :
    (n \in Marked \cup Frontier) <=> Path(n)

PartialCorrectness ==
  /\ pc = "done"
  /\ Marked = { n \in Nodes : Path(n) }

(*-----------------------------------------------------------------
  Liveness property: termination
-----------------------------------------------------------------*)
Termination == <> (pc = "done")

====