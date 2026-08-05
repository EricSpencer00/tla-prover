---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

ReachableSet(S) == {x \in Nodes : \E k \in 1 .. Cardinality(S) : S[k] = x}
NextOf(S) == UNION {Succ[x] : x \in S}

Init ==
  /\ marked = {}
  /\ frontier = <<Root>>
  /\ pc = "running"

Explore(n) ==
  /\ pc = "running"
  /\ \E i \in DOMAIN frontier :
       /\ frontier[i] = n
       /\ IF n \notin marked
          THEN /\ marked' = marked \cup {n}
               /\ frontier' = frontier \o<<>> \o <<x \in Succ[n] : x \notin (marked \cup ReachableSet(frontier))>>
          ELSE /\ frontier' = frontier[1 .. i - 1] \o frontier[i + 1 .. DOMAIN frontier]
               /\ marked' = marked
  /\ pc' = pc

Terminate ==
  /\ pc = "running"
  /\ frontier = <<>>
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Explore(NEXT) \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Explore(NEXT))

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \in FiniteSequences(Nodes)
  /\ pc \in {"running", "done"}

Inv1 ==
  \A x \in marked : NextOf({x}) \subseteq marked \cup ReachableSet(frontier)

Inv2 ==
  ReachableSet(marked \cup ReachableSet(frontier)) = ReachableSet(marked) \cup ReachableSet(frontier)

Inv3 ==
  ReachableSet({Root}) = marked \cup ReachableSet(frontier)

PartialCorrectness ==
  pc = "done" => ReachableSet({Root}) = marked

Termination ==
  (\A x \in ReachableSet({Root}) : x \in Nodes)
    ~> (pc = "done")
====