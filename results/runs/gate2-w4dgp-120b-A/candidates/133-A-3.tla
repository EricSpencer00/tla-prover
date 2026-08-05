---- MODULE MCParReach ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succ
vars == <<marked, frontier, pc, sel, succ>>

Init ==
  /\ marked = {[n \in Nodes |-> FALSE]}
  /\ frontier = <<"Root">>
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> <<>>]
  /\ succ = [p \in Procs |-> <<>>]

InitP ==
  /\ Init
  /\ frontier[1] = Root

RollSucc ==
  /\ \E p \in Procs, w \in Nodes :
       /\ pc[p] = "idle"
       /\ marked[w]
       /\ pc' = [pc EXCEPT ![p] = "roll"]
       /\ succ' = [succ EXCEPT ![p] = <<w>>]
  /\ UNCHANGED <<marked, frontier, sel>>

AdvanceP ==
  /\ \E p \in Procs, b \in Nodes, c \in Nodes :
       /\ pc[p] = "roll"
       /\ Len(succ[p]) < 2
       /\ succ' = [succ EXCEPT ![p] = Append(succ[p], b)]
  /\ UNCHANGED <<marked, frontier, pc, sel>>

ApplyP ==
  /\ \E p \in Procs :
       /\ pc[p] = "roll"
       /\ marked' = [marked EXCEPT ![succ[p][1]] = TRUE]
       /\ frontier' = Append(frontier, succ[p][1])
       /\ succ' = [succ EXCEPT ![p] = Tail(succ[p])]
  /\ UNCHANGED <<pc, sel>>

ResetP ==
  /\ \E p \in Procs :
       /\ pc[p] = "roll"
       /\ succ[p] = <<>>
       /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<marked, frontier, sel, succ>>

InitS ==
  /\ Init
  /\ frontier = <<Root>>

RollSeq ==
  /\ \E p \in Procs, w \in Nodes:
       /\ pc[p] = "idle"
       /\ marked[w]
       /\ pc' = [pc EXCEPT ![p] = "roll"]
       /\ sel' = [sel EXCEPT ![p] = <<w>>]
  /\ UNCHANGED <<marked, frontier, succ>>

AdvanceS ==
  /\ \E p \in Procs, b \in Nodes :
       /\ pc[p] = "roll"
       /\ Len(sel[p]) < 2
       /\ sel' = [sel EXCEPT ![p] = Append(sel[p], b)]
  /\ UNCHANGED <<marked, frontier, pc, succ>>

ApplyS ==
  /\ \E p \in Procs :
       /\ pc[p] = "roll"
       /\ marked' = [marked EXCEPT ![sel[p][1]] = TRUE]
       /\ frontier' = Append(frontier, sel[p][1])
       /\ sel' = [sel EXCEPT ![p] = Tail(sel[p])]
  /\ UNCHANGED <<pc, succ>>

ResetS ==
  /\ \E p \in Procs :
       /\ pc[p] = "roll"
       /\ sel[p] = <<>>
       /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<marked, frontier, succ, sel>>

Next == RollSucc \/ AdvanceP \/ ApplyP \/ ResetP \/ RollSeq \/ AdvanceS \/ ApplyS \/ ResetS

Spec == InitP /\ InitS /\ [][Next]_vars

Inv ==
  /\ \A p \in Procs : pc[p] \in {"idle", "roll"}
  /\ Len(frontier) <= 4
  /\ frontier[1] = Root
  /\ \A i \in DOMAIN frontier : marked[frontier[i]]
  /\ \A p \in Procs :
       /\ pc[p] = "idle" => sel[p] = succ[p]
       /\ pc[p] = "roll" => sel[p] # succ[p]

Refines ==
  \A b \in Nodes : marked[b] => b \in ConnectedToSomeButNotAll

====