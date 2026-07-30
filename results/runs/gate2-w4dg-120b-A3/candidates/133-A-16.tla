---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

Control == {"idle", "selecting", "exploring", "done"}

Marked == [Nodes -> BOOLEAN]
Frontier == [Nodes -> BOOLEAN]
Prog == [Procs -> Control]

InitBound == Cardinality(Nodes)

Init ==
  /\ marked = [n \in Nodes |-> FALSE]
  /\ frontier = [n \in Nodes |-> n = Root]
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> CHOOSE n \in Nodes : TRUE]
  /\ succs = [p \in Procs |-> <<>>]

BeginSelect(p) ==
  /\ pc[p] = "idle"
  /\ \E n \in Nodes :
       /\ frontier[n]
       /\ sel' = [sel EXCEPT ![p] = n]
  /\ pc' = [pc EXCEPT ![p] = "selecting"]
  /\ UNCHANGED <<marked, frontier, succs>>

BeginExplore(p) ==
  /\ pc[p] = "selecting"
  /\ frontier' = [frontier EXCEPT ![sel[p]] = FALSE]
  /\ marked' = [marked EXCEPT ![sel[p]] = TRUE]
  /\ pc' = [pc EXCEPT ![p] = "exploring"]
  /\ UNCHANGED <<sel, succs>>

Explore(p) ==
  /\ pc[p] = "exploring"
  /\ succs' = [succs EXCEPT ![p] = IF Len(succs[p]) < InitBound THEN succs[p] \o <<sel[p]>> ELSE succs[p]]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<marked, frontier, sel>>

TryAgain(p) ==
  /\ pc[p] = "done"
  /\ frontier' = [n \in Nodes |-> frontier[n] \/ ~marked[n]]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ succs' = [succs EXCEPT ![p] = <<>>]
  /\ UNCHANGED <<marked, sel>>

Next ==
  \/ \E p \in Procs : BeginSelect(p)
  \/ \E p \in Procs : BeginExplore(p)
  \/ \E p \in Procs : Explore(p)
  \/ \E p \in Procs : TryAgain(p)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ \A n \in Nodes : marked[n] => (frontier[n] \/ \E p \in Procs : sel[p] = n)
  /\ \A p \in Procs : pc[p] # "idle" => frontier[sel[p]]
  /\ \A p \in Procs : pc[p] = "idle" => frontier[sel[p]]

Refines == TRUE

ConnectedToSomeButNotAll ==
  Succ

LimitedSeq == Seq

====