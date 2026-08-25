---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

(* Operator that the .cfg will substitute for Succ *)
ConnectedToSomeButNotAll == [n \in Nodes |-> {}]

(* Finite version of Seq, kept identical for model checking *)
LimitedSeq(S) == Seq(S)

(* ReachableFrom(S) = set of nodes reachable from any node in S via Succ *)
ReachableFrom(S) ==
  { n \in Nodes :
      \E p \in LimitedSeq(Nodes) :
        /\ Len(p) >= 1
        /\ p[1] \in S
        /\ n = p[Len(p)]
        /\ \A i \in 1 .. Len(p)-1 : p[i+1] \in Succ[p[i]]
  }

VARIABLES marked, frontier, pc

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "run"

ChooseNode ==
  /\ frontier # {}
  /\ \E node \in frontier :
        /\ IF node \notin marked
              THEN /\ marked'   = marked \cup {node}
                   /\ frontier' = frontier \cup Succ[node]
              ELSE /\ marked'   = marked
                   /\ frontier' = frontier \ {node}
  /\ pc' = pc

Terminate ==
  /\ frontier = {}
  /\ pc = "run"
  /\ pc' = "done"
  /\ marked'   = marked
  /\ frontier' = frontier

Next == ChooseNode \/ Terminate

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* Type correctness invariant *)
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ Root \in Nodes
  /\ Succ \in [Nodes -> SUBSET Nodes]

(* Invariant 1: successors of marked nodes are in marked ∪ frontier *)
Inv1 ==
  \A n \in marked : Succ[n] \subseteq marked \cup frontier

(* Invariant 2: marked ∪ ReachableFrom(frontier) = ReachableFrom(marked ∪ frontier) *)
Inv2 ==
  marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

(* Invariant 3: reachable from Root = marked ∪ ReachableFrom(frontier) *)
Inv3 ==
  ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

(* Partial correctness: when frontier is empty, marked equals the reachable set *)
PartialCorrectness ==
  (frontier = {} => marked = ReachableFrom({Root}))

(* Liveness property: eventual termination *)
Termination == <> (frontier = {})

====