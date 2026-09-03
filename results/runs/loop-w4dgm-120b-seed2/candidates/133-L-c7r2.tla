---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

ASSUME Root \in Nodes

VARIABLES marked, frontier, pc, chosen, succs

vars == <<marked, frontier, pc, chosen, succs>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> {"idle", "holding", "reading", "exploring"}]
    /\ chosen \in [Procs -> Nodes \cup {"none"}]
    /\ succs \in [Nodes -> SUBSET Nodes]

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "idle"]
    /\ chosen = [p \in Procs |-> "none"]
    /\ succs = [n \in Nodes |-> Succ(n)]

Acquire ==
    /\ \E p \in Procs, n \in frontier :
         /\ pc[p] = "idle"
         /\ pc' = [pc EXCEPT ![p] = "holding"]
         /\ chosen' = [chosen EXCEPT ![p] = n]
    /\ UNCHANGED <<marked, frontier, succs>>

Release ==
    /\ \E p \in Procs :
         /\ pc[p] = "holding"
         /\ pc' = [pc EXCEPT ![p] = "idle"]
         /\ chosen' = [chosen EXCEPT ![p] = "none"]
    /\ UNCHANGED <<marked, frontier, succs>>

Read ==
    /\ \E p \in Procs :
         /\ pc[p] = "holding"
         /\ pc' = [pc EXCEPT ![p] = "reading"]
         /\ succs' = [succs EXCEPT ![chosen[p]] = ConnectedToSomeButNotAll(chosen[p])]
    /\ UNCHANGED <<marked, frontier, chosen>>

Explore ==
    /\ \E p \in Procs :
         /\ pc[p] = "reading"
         /\ \E t \in succs[chosen[p]] :
              /\ t \notin marked
              /\ marked' = marked \cup {t}
              /\ frontier' = frontier \cup {t}
         /\ frontier' = frontier \ {chosen[p]}
         /\ pc' = [pc EXCEPT ![p] = "exploring"]
    /\ UNCHANGED <<chosen, succs>>

Finish ==
    /\ \E p \in Procs :
         /\ pc[p] = "exploring"
         /\ pc' = [pc EXCEPT ![p] = "idle"]
         /\ chosen' = [chosen EXCEPT ![p] = "none"]
    /\ UNCHANGED <<marked, frontier, succs>>

Spec == Init /\ [][\E a \in {Acquire, Release, Read, Explore, Finish} : a]_vars

RECURSIVE SpanOf(_)
SpanOf(S) ==
    IF S = {} THEN {}
    ELSE LET n == CHOOSE e \in S : TRUE IN {n} \cup SpanOf(S \ {n}) \cup succs[n]

BoundedSpan == Cardinality(SpanOf({Root})) <= Cardinality(Nodes)

Inv == TypeOK /\ BoundedSpan

Refines == BoundedSpan

Succ(n) == {m \in Nodes : (n, m) \in Succ}

ConnectedToSomeButNotAll(n) == Succ(n)

LimitedSeq == Seq

====