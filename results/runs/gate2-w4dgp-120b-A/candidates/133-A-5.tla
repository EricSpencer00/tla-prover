---- MODULE MCParReach ----
EXTENDS Integers, FiniteSets, Sequences, MCParReachBase

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, chosen, succs

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "exploring", "done"}]
  /\ chosen \in [Procs -> Seq(Nodes)]
  /\ succs \in [Procs -> Seq(Nodes)]

ControlFlow ==
  /\ \A q \in Procs : pc[q] = "exploring" => chosen[q] # << >>
  /\ \A q \in Procs : pc[q] = "exploring" /\ Cardinality(chosen[q]) = 2 => chosen[q] # << >>
  /\ \A q \in Procs : pc[q] = "done" => frontier = {}
  /\ \A q \in Procs : frontier = {} => pc[q] = "done"

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = [q \in Procs |-> "idle"]
  /\ chosen = [q \in Procs |-> << >>]
  /\ succs = [q \in Procs |-> << >>]

Exploring(q) ==
  /\ pc[q] = "idle"
  /\ frontier # {}
  /\ \E n \in frontier :
       /\ n \notin marked
       /\ chosen' = [chosen EXCEPT ![q] = Append(chosen[q], n)]
       /\ marked' = marked \cup {n}
       /\ frontier' = frontier \ {n}
       /\ succs' = [succs EXCEPT ![q] = << >>]
  /\ pc' = [pc EXCEPT ![q] = "exploring"]

ChooseSuccessors(q) ==
  /\ pc[q] = "exploring"
  /\ succs[q] = << >>
  /\ \E s \in Succ[CHOOSE n \in Nodes : n = chosen[q][Len(chosen[q])]] :
       succs' = [succs EXCEPT ![q] = << s >>]
  /\ UNCHANGED <<marked, frontier, pc, chosen>>

ExploreSuccessors(q) ==
  /\ pc[q] = "exploring"
  /\ succs[q] # << >>
  /\ frontier' = frontier \cup {Head(succs[q])}
  /\ succs' = [succs EXCEPT ![q] = Tail(succs[q])]
  /\ UNCHANGED <<marked, pc, chosen>>

Finish(q) ==
  /\ pc[q] = "exploring"
  /\ chosen[q] # << >>
  /\ Cardinality(chosen[q]) = 2
  /\ pc' = [pc EXCEPT ![q] = "done"]
  /\ chosen' = [chosen EXCEPT ![q] = << >>]
  /\ succs' = [succs EXCEPT ![q] = << >>]
  /\ UNCHANGED <<marked, frontier>>

Done ==
  /\ frontier = {}
  /\ \A q \in Procs : pc[q] = "done"
  /\ UNCHANGED <<marked, frontier, pc, chosen, succs>>

Next ==
  \/ \E q \in Procs : Exploring(q)
  \/ \E q \in Procs : ChooseSuccessors(q)
  \/ \E q \in Procs : ExploreSuccessors(q)
  \/ \E q \in Procs : Finish(q)
  \/ Done

Spec == Init /\ [][Next]_<<marked, frontier, pc, chosen, succs>>

Inv == TypeOK /\ ControlFlow

Refines == RefinesSeq

ConnectedToSomeButNotAll == Succ

LimitedSeq == Seq

====