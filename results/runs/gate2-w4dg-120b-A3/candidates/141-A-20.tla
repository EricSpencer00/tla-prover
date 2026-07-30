---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

Queued == "queued"

VARIABLES marked, frontier, pc
vars == << marked, frontier, pc >>

RECURSIVE ReachFrom(_)
ReachFrom(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE
           rest == ReachFrom(S \ {x})
       IN {x} \cup {z \in Nodes : \E y \in S : z \in Succ[y]} \cup rest

RECURSIVE FrontierReach(_)
FrontierReach(F) ==
  IF F = {} THEN {}
  ELSE LET f == CHOOSE x \in F : TRUE
           rest == FrontierReach(F \ {f})
       IN {f} \cup {z \in Nodes : \E y \in F : z \in Succ[y]} \cup rest

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

Explore ==
  /\ pc = "running"
  /\ frontier # {}
  /\ \E v \in frontier :
       /\ IF v \notin marked
            THEN /\ marked' = marked \cup {v}
                 /\ frontier' = frontier \cup Succ[v]
            ELSE /\ marked' = marked
                 /\ frontier' = frontier \ {v}
  /\ pc' = IF frontier' = {} THEN "done" ELSE "running"

Next ==
  /\ Explore
  /\ UNCHANGED << >>

Spec == Init /\ [][Next]_vars

Inv1 ==
  \A v \in marked : \A w \in Succ[v] : w \in marked \/ frontier

Inv2 ==
  (marked \cup frontier) = ReachFrom(marked \cup frontier)
    /\ FrontierReach(frontier) = ReachFrom(frontier)

Inv3 ==
  ReachFrom({Root}) = marked \cup FrontierReach(frontier)

PartialCorrectness ==
  (pc = "done") => (marked = ReachFrom({Root}))

Termination == (<> (pc = "done"))

LimitedSeq ==
  /\ \A n \in Nat : Len(Seq(n)) = n
  /\ \A n \in Nat : \A i \in 1..n : Seq(n)[i] \in Nodes

Succ == ConnectedToSomeButNotAll

====