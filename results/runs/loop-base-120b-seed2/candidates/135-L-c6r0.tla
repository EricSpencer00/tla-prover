---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES Marked, Frontier, pc

vars == <<Marked, Frontier, pc>>

(*--- Initial state ---*)
Init ==
    /\ Marked = {Root}
    /\ Frontier = ConnectedToSomeButNotAll(Root)
    /\ pc = "step"

(*--- Next-state relation ---*)
Next ==
    \/ /\ pc = "step"
       /\ Frontier # {}
       /\ LET n == CHOOSE x \in Frontier : TRUE IN
          /\ Marked'   = Marked \cup {n}
          /\ Frontier' = (Frontier \ {n}) \cup (ConnectedToSomeButNotAll(n) \ Marked)
          /\ pc'       = "step"
    \/ /\ pc = "step"
       /\ Frontier = {}
       /\ pc' = "done"
       /\ UNCHANGED <<Marked, Frontier>>

Spec == Init /\ [][Next]_vars

(*--- Type correctness invariant ---*)
TypeOK ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ pc \in {"init", "step", "done"}

(*--- Algorithm invariants ---*)
Inv1 == \A n \in Marked :
           ConnectedToSomeButNotAll(n) \subseteq Marked \cup Frontier

Inv2 == Frontier \cap Marked = {}

Inv3 == (pc # "done") => (Root \in Marked \/ Root \in Frontier)

(*--- Partial correctness property ---*)
PartialCorrectness ==
    (pc = "done") =>
        Marked = { n \in Nodes :
                    \E s \in LimitedSeq :
                        Len(s) >= 1 /\ s[1] = Root /\ s[Len(s)] = n /\
                        \A i \in 1..Len(s)-1 :
                           s[i+1] \in ConnectedToSomeButNotAll(s[i])
                 }

(*--- Liveness property (termination) ---*)
Termination == <> (pc = "done")

(*--- Operators substituted by the .cfg ---*)
ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq == { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

====