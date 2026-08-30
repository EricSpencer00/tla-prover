---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

NONE == "none"

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

SuccSet(n) == Succ[n]

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> NONE]
  /\ succs = [p \in Procs |-> {}]

Select(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ pc' = [pc EXCEPT ![p] = "active"]
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ UNCHANGED <<marked, frontier>>

Explore(p) ==
  /\ pc[p] = "active"
  /\ sel[p] \in frontier
  /\ frontier' = frontier \ {sel[p]}
  /\ pc' = [pc EXCEPT ![p] = "exploring"]
  /\ UNCHANGED <<marked, sel, succs>>

RecordSuccessor(p, m) ==
  /\ pc[p] = "exploring"
  /\ m \in SuccSet(sel[p])
  /\ succs' = [succs EXCEPT ![p] = succs[p] \cup {m}]
  /\ UNCHANGED <<marked, frontier, pc, sel>>

FinishExploring(p) ==
  /\ pc[p] = "exploring"
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ frontier' = frontier \cup succs[p]
  /\ UNCHANGED <<marked, sel, succs>>

Commit(p) ==
  /\ pc[p] = "done"
  /\ sel[p] \notin marked
  /\ marked' = marked \cup {sel[p]}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = NONE]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ UNCHANGED frontier

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs : Explore(p)
  \/ \E p \in Procs, m \in Nodes : RecordSuccessor(p, m)
  \/ \E p \in Procs : FinishExploring(p)
  \/ \E p \in Procs : Commit(p)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ frontier \cap marked = {}
  /\ \A p \in Procs : pc[p] \in {"idle", "active", "exploring", "done"}
  /\ \A p \in Procs :
        pc[p] = "idle" => (sel[p] = NONE /\ succs[p] = {})
  /\ \A p \in Procs : pc[p] = "active" => sel[p] \in frontier
  /\ \A p \in Procs : pc[p] \in {"exploring", "done"} => (sel[p] \in Nodes /\ succs[p] \subseteq SuccSet(sel[p]))

Refines ==
  \A p \in Procs : pc[p] \in {"idle", "active"}

LimitedSeq(n) == CHOOSE s \in Seq(n) : \A i \in DOMAIN s : s[i] \in n

ConnectedToSomeButNotAll(n) == CHOOSE m \in SuccSet(n) : TRUE

====