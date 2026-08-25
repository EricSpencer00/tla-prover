---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

(* Concrete graph: each node has exactly two successors *)
ConnectedToSomeButNotAll ==
  [n \in Nodes |-> 
    IF n = 0 THEN {1, 2}
    ELSE IF n = 1 THEN {0, 3}
    ELSE IF n = 2 THEN {0, 3}
    ELSE {1, 2}
  ]

(* Bounded sequence operator for model checking *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Reachability using bounded sequences *)
Reachable(a, b) ==
  \E s \in LimitedSeq(Nodes) :
    /\ Len(s) > 0
    /\ s[1] = a
    /\ s[Len(s)] = b
    /\ \A i \in 1..Len(s)-1 : s[i+1] \in ConnectedToSomeButNotAll[s[i]]

VARIABLES marked, frontier, pc

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "Explore"

Expand ==
  /\ pc = "Explore"
  /\ frontier # {}
  /\ LET n == CHOOSE x \in frontier IN
       /\ marked'   = marked \cup {n}
       /\ frontier' = (frontier \ {n}) \cup (ConnectedToSomeButNotAll[n] \ marked)
  /\ UNCHANGED pc

Done ==
  /\ pc = "Explore"
  /\ frontier = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<marked, frontier>>

Next == Expand \/ Done

vars == <<marked, frontier, pc>>

Spec == Init /\ [][Next]_vars

(* Invariants *)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"Explore", "Done"}

Inv1 == \A n \in marked : ConnectedToSomeButNotAll[n] \subseteq marked \cup frontier

Inv2 == Root \in marked

Inv3 == (pc = "Done") => marked = Nodes

PartialCorrectness ==
  (pc = "Done") => \A n \in Nodes : Reachable(Root, n) => n \in marked

(* Liveness property *)

Termination == <> (pc = "Done")

====