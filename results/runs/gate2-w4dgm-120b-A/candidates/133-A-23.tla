---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> {}]

Read(p) ==
  /\ pc[p] = "idle"
  /\ \E n \in frontier :
       /\ sel' = [sel EXCEPT ![p] = n]
       /\ frontier' = frontier \ {n}
  /\ pc' = [pc EXCEPT ![p] = "read"]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ UNCHANGED marked

Select(p) ==
  /\ pc[p] = "read"
  /\ \E m \in ConnectedToSomeButNotAll(n) :
       /\ succs' = [succs EXCEPT ![p] = succs[p] \cup {m}]
  /\ UNCHANGED <<marked, frontier, pc, sel>>

Commit(p) ==
  /\ pc[p] = "read"
  /\ frontier' = frontier \cup succs[p]
  /\ marked' = marked \cup succs[p]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ UNCHANGED sel

Abort(p) ==
  /\ pc[p] = "read"
  /\ frontier' = frontier \cup succs[p]
  /\ marked' = marked \cup succs[p]
  /\ frontier' = frontier \cup {sel[p]}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ UNCHANGED sel

Next == \E p \in Procs : Read(p) \/ Select(p) \/ Commit(p) \/ Abort(p)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ marked \cap frontier = {}
  /\ \A p \in Procs : succs[p] \subseteq Nodes
  /\ \A p \in Procs : pc[p] = "read" => sel[p] # "none"

Refines == \A n \in Nodes : n \in marked

FiniteSeq(S) == {S[i] : i \in 1..Len(S)}

ConnectedToSomeButNotAll ==
  \X n \in Nodes : FiniteSeq(Succ[n])

====