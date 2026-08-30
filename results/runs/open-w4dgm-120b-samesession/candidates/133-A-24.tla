------------------------- MODULE MCParReach -------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succs
vars == <<marked, frontier, pc, sel, succs>>

SuccOf(n) == CHOOSE s \in Succ : s.head = n

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \in SubSeq(ConnectedToSomeButNotAll)
  /\ pc \in [Procs -> {"idle", "selecting", "exploring"}]
  /\ sel \in [Procs -> Nodes]
  /\ succs \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {}
  /\ frontier = <<Root>>
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> Root]
  /\ succs = [p \in Procs |-> ConnectedToSomeButNotAll]

Select(p) ==
  /\ pc[p] = "idle"
  /\ frontier # <<>>
  /\ sel' = [sel EXCEPT ![p] = Head(frontier)]
  /\ frontier' = Tail(frontier)
  /\ pc' = [pc EXCEPT ![p] = "selecting"]
  /\ succs' = [succs EXCEPT ![p] = ConnectedToSomeButNotAll]
  /\ UNCHANGED marked

Explore(p) ==
  /\ pc[p] = "selecting"
  /\ \E c \in succs[p] :
       /\ marked' = marked \cup {c}
       /\ frontier' = LimitedSeq(frontier \circ <<c>>)
  /\ succs' = [succs EXCEPT ![p] = ConnectedToSomeButNotAll \ {sel[p]}]
  /\ pc' = [pc EXCEPT ![p] = "exploring"]
  /\ UNCHANGED sel

Restart(p) ==
  /\ pc[p] = "exploring"
  /\ succs[p] = {}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<marked, frontier, sel, succs>>

Next == \E p \in Procs : Select(p) \/ Explore(p) \/ Restart(p)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ TypeOK
  /\ \A p \in Procs : pc[p] = "selecting" => (sel[p] \notin marked /\ succs[p] = ConnectedToSomeButNotAll)

Refines == \A n \in Nodes : n \in marked => \E p \in Procs : sel[p] = n

LimitedSeq(s) == IF Len(s) < Cardinality(Nodes) THEN s ELSE s
ConnectedToSomeButNotAll == SuccOf(Root).succ
=============================================================================