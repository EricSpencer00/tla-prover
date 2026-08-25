---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

(*--- Concrete graph: each node has exactly two successors ---*)
ConnectedToSomeButNotAll == 
  [n \in Nodes |-> {
        (n % 4) + 1,
        ((n + 1) % 4) + 1
  }]

(*--- Finite version of Seq for model checking ---*)
LimitedSeq == { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

VARIABLES Marked, Frontier, pc
vars == <<Marked, Frontier, pc>>

(*--- Initialization ---*)
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "step"

(*--- One step of the sequential Misra reachability algorithm ---*)
Next ==
  \/ /\ Frontier = {}
     /\ pc' = "done"
     /\ UNCHANGED <<Marked, Frontier>>
  \/ /\ Frontier # {}
     /\ \E v \in Frontier :
        LET newSucc == ConnectedToSomeButNotAll[v] IN
          /\ Marked'   = Marked \cup {v} \cup newSucc
          /\ Frontier' = (Frontier \ {v}) \cup (newSucc \ Marked)
          /\ pc'       = "step"

Spec == Init /\ [][Next]_vars

(*--- Type correctness invariant ---*)
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"step", "done"}

(*--- Reachable nodes defined via bounded sequences ---*)
Reachable ==
  { n \in Nodes :
      \E s \in LimitedSeq :
        /\ Len(s) > 0
        /\ s[1] = Root
        /\ s[Len(s)] = n
        /\ \A i \in 1..(Len(s) - 1) :
              s[i+1] \in ConnectedToSomeButNotAll[s[i]]
  }

(*--- Invariant 1: successor closure ---*)
Inv1 == \A n \in Marked : ConnectedToSomeButNotAll[n] \subseteq Marked

(*--- Invariant 2: Marked equals the set of reachable nodes ---*)
Inv2 == Marked = Reachable

(*--- Invariant 3: When finished, Marked equals Reachable ---*)
Inv3 == (pc = "done") => Marked = Reachable

(*--- Partial correctness: the root is always marked when done ---*)
PartialCorrectness == (pc = "done") => Root \in Marked

(*--- Liveness: the algorithm eventually terminates ---*)
Termination == <> (pc = "done")

====