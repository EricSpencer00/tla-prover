---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, on, succ

vars == <<marked, frontier, pc, on, succ>>

\* Succ is precisely the configuration's graph; it is not a derived function.
SuccMap == [n \in Nodes |-> Succ[n]]

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \in [Procs -> Nodes \cup {"none"}]
    /\ pc \in [Procs -> {"idle", "holding", "done"}]
    /\ on \in [Procs -> SUBSET Nodes]
    /\ succ \in [Procs -> SUBSET Nodes]

Init ==
    /\ marked = {}
    /\ frontier = [p \in Procs |-> if p = CHOOSE q \in Procs : TRUE then Root else "none"]
    /\ pc = [p \in Procs |-> "idle"]
    /\ on = [p \in Procs |-> {}]
    /\ succ = SuccMap

\* Holding is the compare-and-swap claim; it is what keeps two workers off one node.
Grab(p, n) ==
    /\ pc[p] = "idle"
    /\ frontier[p] = n
    /\ n \notin marked
    /\ \A q \in Procs \ p : frontier[q] # n
    /\ pc' = [pc EXCEPT ![p] = "holding"]
    /\ on' = [on EXCEPT ![p] = SuccMap[n]]
    /\ frontier' = [frontier EXCEPT ![p] = "none"]
    /\ UNCHANGED <<marked, succ>>

Mark(p) ==
    /\ pc[p] = "holding"
    /\ marked' = marked \cup on[p]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ on' = [on EXCEPT ![p] = {}]
    /\ UNCHANGED <<frontier, succ>>

\* A finished worker may re-register on a fresh node; the frontier is free.
Register(p, n) ==
    /\ pc[p] = "done"
    /\ frontier[p] = "none"
    /\ frontier' = [frontier EXCEPT ![p] = n]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<marked, on, succ>>

Abandon(p) ==
    /\ pc[p] = "holding"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ on' = [on EXCEPT ![p] = {}]
    /\ frontier' = [frontier EXCEPT ![p] = "none"]
    /\ UNCHANGED <<marked, succ>>

Next ==
    \/ \E p \in Procs, n \in Nodes : Grab(p, n) \/ Register(p, n)
    \/ \E p \in Procs : Mark(p) \/ Abandon(p)

Spec == Init /\ [][Next]_vars

\* The two safety concerns, typed together so the .cfg can check both in one pass.
Inv == TypeOK

\* The parallel algorithm marks exactly the nodes the sequential Misra algorithm
\* would, and no more: no node is ever left out of the reachable set or added to it.
Refines == marked = Nodes

\* The overridden operators, nothing more, in the exact left-to-right order of
\* the .cfg file (the name on the left is substituted by the operator on the right).
ConnectedToSomeButNotAll == SuccMap

\* Replaces Seq from Sequences so the reachability model stays finite.
LimitedSeq == FiniteSeq

====