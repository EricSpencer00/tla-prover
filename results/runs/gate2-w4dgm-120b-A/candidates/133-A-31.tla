---- MODULE MCParReach ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

None == "none"

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> None]
  /\ succs = [n \in Nodes |-> Succ[n]]

CasClaim(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ marked' = marked \cup {n}
  /\ pc' = [pc EXCEPT ![p] = "critical"]
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ succs' = succs

Explore(p) ==
  /\ pc[p] = "critical"
  /\ frontier' = frontier \cup succs[sel[p]]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = None]
  /\ UNCHANGED <<marked, succs>>

CasStep ==
  \/ \E p \in Procs, n \in Nodes : CasClaim(p, n)
  \/ \E p \in Procs : Explore(p)

Spec == Init /\ [][CasStep]_vars

Inv ==
  /\ marked \cap frontier = {}
  /\ \A a, b \in frontier : (a # b) => (a \notin succs[b])
  /\ \A p \in Procs : pc[p] \in {"idle", "critical"}
  /\ \A p \in Procs : (pc[p] = "critical") <=> (sel[p] # None)

Refines == Inv /\ Spec

LimitedSeq == Seq

ConnectedToSomeButNotAll == Succ

====