---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences, Reachability

CONSTANTS Nodes, Root, Succ

ASSUME Root \in Nodes

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = 0

Traverse ==
  /\ pc = 0
  /\ frontier # {}
  /\ \E n \in frontier :
       LET newfr == (Succ[n] \ marked) \cup (frontier \ {n}) IN
         /\ marked' = marked \cup Succ[n]
         /\ frontier' = newfr
  /\ pc' = 1

Advance ==
  /\ pc = 1
  /\ frontier # {}
  /\ pc' = 0
  /\ UNCHANGED <<marked, frontier>>

Idle ==
  /\ frontier = {}
  /\ pc' = 2
  /\ UNCHANGED <<marked, frontier>>

Next == Traverse \/ Advance \/ Idle

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in 0..2

Inv1 ==
  \A n \in Nodes : n \in frontier => n \in marked

Inv2 ==
  \A n \in marked :
    (n = Root) \/ (\E m \in marked : n \in Succ[m])

Inv3 ==
  \A n \in Nodes :
    (\E s \in FiniteSequences(Nodes) :
       /\ Len(s) >= 1
       /\ s[1] = Root
       /\ s[Len(s)] = n
       /\ \A i \in 1..(Len(s) - 1) : s[i + 1] \in Succ[s[i]]
    ) => n \in marked

PartialCorrectness ==
  \A n \in Nodes :
    (\E s \in FiniteSequences(Nodes) :
       /\ Len(s) >= 1
       /\ s[1] = Root
       /\ s[Len(s)] = n
       /\ \A i \in 1..(Len(s) - 1) : s[i + 1] \in Succ[s[i]]
    ) => n \in marked

Termination == <>(pc = 2)

Invariants == TypeOK /\ Inv1 /\ Inv2 /\ Inv3 /\ PartialCorrectness
====