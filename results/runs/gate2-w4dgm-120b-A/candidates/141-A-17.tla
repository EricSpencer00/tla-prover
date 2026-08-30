---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "terminated"}
  /\ Root \in Nodes

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

Res == UNION {Succ(n) : n \in marked}
FrontierRes == UNION {Succ(n) : n \in frontier}

Inv1 == Res \subseteq (marked \cup frontier)
Inv2 == (marked \cup frontier) \subseteq (marked \cup FrontierRes)
Inv3 ==
  /\ Res \subseteq marked
  /\ FrontierRes \subseteq marked \union frontier
PartialCorrectness == Res \subseteq marked

Work(n) ==
  \/ /\ n \in frontier
     /\ n \notin marked
     /\ marked' = marked \union {n}
     /\ frontier' = frontier \union Succ(n)
     /\ pc' = pc
  \/ /\ n \in frontier
     /\ n \in marked
     /\ frontier' = frontier \ {n}
     /\ marked' = marked
     /\ pc' = pc

Next == \E n \in Nodes : Work(n)

Terminate ==
  /\ frontier = {}
  /\ pc = "running"
  /\ pc' = "terminated"
  /\ marked' = marked
  /\ frontier' = frontier
  /\ \A n \in Nodes : UNCHANGED Work(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Terminate)

Termination == marked # Nodes => <>(marked = Nodes)

ConnectedToSomeButNotAll == CHOOSE f \in [Nodes -> SUBSET Nodes] :
  /\ \A n \in Nodes : f[n] \subseteq Nodes
  /\ \A n \in Nodes : \A m \in f[n] : f[m] \subseteq f[n]
  /\ \A n \in Nodes : \A m \in Nodes : n \in f[m] => m \in f[n]
  /\ Cardinality(f[Root]) = Cardinality(Nodes)

All == UNION { ConnectedToSomeButNotAll[n] : n \in Nodes }
LimitedSeq == CHOOSE s \in Sequences(All) :
  \A a \in All : \E i \in DOMAIN s : s[i] = a
====