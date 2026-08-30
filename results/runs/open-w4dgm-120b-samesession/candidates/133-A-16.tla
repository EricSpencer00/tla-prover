---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

None == "none"

VARIABLES marked, frontier, pc, chosen, succs

vars == <<marked, frontier, pc, chosen, succs>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> {"idle", "working", "waiting", "done"}]
    /\ chosen \in [Procs -> Nodes \cup {None}]
    /\ succs \in [Procs -> Seq(Nodes]]

WellFormed ==
    /\ frontier \subseteq marked
    /\ \A i \in Procs : pc[i] = "working" => chosen[i] \in Nodes

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = [i \in Procs |-> "idle"]
    /\ chosen = [i \in Procs |-> None]
    /\ succs = [i \in Procs |-> << >>]

Choose(i, n) ==
    /\ pc[i] = "idle"
    /\ n \in frontier
    /\ pc' = [pc EXCEPT ![i] = "working"]
    /\ chosen' = [chosen EXCEPT ![i] = n]
    /\ succs' = [succs EXCEPT ![i] = << >>]
    /\ UNCHANGED <<marked, frontier>>

Expand(i) ==
    /\ pc[i] = "working"
    /\ Len(succs[i]) < Cardinality(Nodes)
    /\ \E m \in Succ[chosen[i]] :
        /\ m \notin marked
        /\ marked' = marked \cup {m}
        /\ frontier' = frontier \cup {m}
        /\ succs' = [succs EXCEPT ![i] = Append(succs[i], m)]
    /\ pc' = [pc EXCEPT ![i] = "waiting"]
    /\ UNCHANGED <<pc, chosen>>

Commit(i) ==
    /\ pc[i] = "waiting"
    /\ frontier' = frontier \ {chosen[i]}
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<marked, chosen, succs>>

Reset(i) ==
    /\ pc[i] = "done"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ chosen' = [chosen EXCEPT ![i] = None]
    /\ succs' = [succs EXCEPT ![i] = << >>]
    /\ UNCHANGED <<marked, frontier>>

ResetAll ==
    /\ \A i \in Procs : pc[i] = "done"
    /\ marked = Nodes
    /\ frontier = {}
    /\ pc' = [i \in Procs |-> "idle"]
    /\ chosen' = [i \in Procs |-> None]
    /\ succs' = [i \in Procs |-> << >>]
    /\ UNCHANGED marked

Next ==
    \/ \E i \in Procs, n \in Nodes : Choose(i, n)
    \/ \E i \in Procs : Expand(i)
    \/ \E i \in Procs : Commit(i)
    \/ \E i \in Procs : Reset(i)
    \/ ResetAll

Spec == Init /\ [][Next]_vars

Inv == WellFormed

Refines == WellFormed

ConnectedToSomeButNotAll ==
    \E i \in Procs : Len(succs[i]) = Cardinality(Nodes)

LimitedSeq == Seq

====