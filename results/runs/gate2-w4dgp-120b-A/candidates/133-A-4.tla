---- MODULE MCParReach ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, nexts

vars == <<marked, frontier, pc, sel, nexts>>

Adjacent(x) == Succ[x]

Init == /\ marked = {Root}
        /\ frontier = {Root}
        /\ pc = [p \in Procs |-> "idle"]
        /\ sel = [p \in Procs |-> 0]
        /\ nexts = [p \in Procs |-> << >>]

Read(p) == /\ pc[p] = "idle"
           /\ frontier # {}
           /\ \E v \in frontier :
                /\ pc' = [pc EXCEPT ![p] = "working"]
                /\ sel' = [sel EXCEPT ![p] = v]
                /\ frontier' = frontier \ {v}
           /\ UNCHANGED <<marked, nexts>>

Expand(p) == /\ pc[p] = "working"
             /\ Cardinality(nexts[p]) < Cardinality(Nodes)
             /\ nexts' = [nexts EXCEPT ![p] = Append(@, sel[p])]
             /\ pc' = [pc EXCEPT ![p] = "read"]
             /\ UNCHANGED <<marked, frontier, sel>>

Write(p) == /\ pc[p] = "read"
            /\ \E w \in Adjacent(sel[p]) :
                 /\ marked' = marked \cup {w}
                 /\ frontier' = frontier \cup {w}
                 /\ nexts' = [nexts EXCEPT ![p] = Tail(@)]
            /\ pc' = [pc EXCEPT ![p] = "idle"]
            /\ UNCHANGED <<sel>>

Next == \E p \in Procs : Read(p) \/ Expand(p) \/ Write(p)

Spec == Init /\ [][Next]_vars

Inv == /\ marked \subseteq Nodes
       /\ frontier \subseteq Nodes
       /\ frontier \cap marked = {}
       /\ pc \in [Procs -> {"idle", "working", "read"}]
       /\ \A p \in Procs : nexts[p] \in Seq(Nodes)

Refines == \A p \in Procs : (pc[p] = "idle" /\ frontier = {}) ~> (\A q \in Procs : pc[q] = "idle")

====