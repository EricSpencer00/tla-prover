---- MODULE MCParReach ----
EXTENDS Integers, Sequences, FiniteSets, UNCHANGED

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> 0]
  /\ succs = [p \in Procs |-> << >>]

Select ==
  /\ \E p \in Procs, n \in frontier :
       /\ pc[p] = "idle"
       /\ frontier' = frontier \ {n}
       /\ sel' = [sel EXCEPT ![p] = n]
       /\ pc' = [pc EXCEPT ![p] = "working"]
       /\ succs' = [succs EXCEPT ![p] = << >>]
  /\ UNCHANGED marked

Load ==
  /\ \E p \in Procs :
       /\ pc[p] = "working"
       /\ Len(succs[p]) < Cardinality(Nodes)
       /\ succs' = [succs EXCEPT ![p] = Append(succs[p], sel[p])]
       /\ pc' = [pc EXCEPT ![p] = "loaded"]
  /\ UNCHANGED <<marked, frontier, sel>>

Commit ==
  /\ \E p \in Procs :
       /\ pc[p] = "loaded"
       /\ frontier' = frontier \cup {sel[p]}
       /\ marked' = marked \cup {sel[p]}
       /\ pc' = [pc EXCEPT ![p] = "idle"]
       /\ sel' = [sel EXCEPT ![p] = 0]
       /\ succs' = [succs EXCEPT ![p] = << >>]

Next == Select \/ Load \/ Commit

Spec == Init /\ [][Next]_vars

Inv ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ \A p \in Procs :
       /\ (pc[p] = "idle" => succs[p] = << >>)
       /\ (pc[p] = "working" => succs[p] = << >>)
       /\ (pc[p] = "loaded" => succs[p] # << >> /\ Len(succs[p]) <= Cardinality(Nodes))
  /\ \A p \in Procs : sel[p] \in Nodes \/ sel[p] = 0

Refines == \A n \in Nodes : n \in marked => \E m \in Nodes : n \in succs[m]

ASSUME ConnectedToSomeButNotAll == Succ

LimitedSeq == [a \in Nodes, k \in 0..Cardinality(Nodes) |-> CHOOSE s \in Seq(a) : Len(s) = k]

====