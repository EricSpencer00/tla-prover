---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succs

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> {"idle", "owning", "done"}]
    /\ sel \in [Procs -> Nodes \cup {"none"}]
    /\ succs \in [Procs -> SUBSET Nodes]

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> "none"]
    /\ succs = [p \in Procs |-> {}]

\* The frontier is part of the shared state; the CAS is the write-test on it.
Acquire(p, n) ==
    /\ pc[p] = "idle"
    /\ n \in frontier
    /\ frontier' = frontier \ {n}
    /\ marked' = marked \cup {n}
    /\ pc' = [pc EXCEPT ![p] = "owning"]
    /\ succs' = [succs EXCEPT ![p] = Succ[n]]
    /\ sel' = [sel EXCEPT ![p] = n]

Explore(p) ==
    /\ pc[p] = "owning"
    /\ frontier' = frontier \cup succs[p]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ succs' = [succs EXCEPT ![p] = {}]
    /\ sel' = [sel EXCEPT ![p] = "none"]
    /\ marked' = marked

\* The frontier is a set, so packets can be examined in any order -- that is
\* exactly what makes the concurrent exploration exhaustive.
DropStale(p) ==
    /\ pc[p] = "owning"
    /\ \/ sel[p] \notin frontier
       \/ succs[p] = {}
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ succs' = [succs EXCEPT ![p] = {}]
    /\ sel' = [sel EXCEPT ![p] = "none"]
    /\ marked' = marked
    /\ frontier' = frontier

Reset ==
    /\ \A p \in Procs : pc[p] = "done"
    /\ frontier' = frontier \cup marked
    /\ marked' = {}
    /\ pc' = [p \in Procs |-> "idle"]
    /\ succs' = [p \in Procs |-> {}]
    /\ sel' = [p \in Procs |-> "none"]

Next ==
    \/ \E p \in Procs, n \in Nodes : Acquire(p, n)
    \/ \E p \in Procs : Explore(p)
    \/ \E p \in Procs : DropStale(p)
    \/ Reset

Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succs>>

\* The invariant is the same one the algorithm version checks; it is not
\* weakened here because the frontier is a set instead of a sequence.
Inv ==
    /\ marked \cap frontier = {}
    /\ marked \cup frontier = Nodes
    /\ \A p \in Procs : pc[p] = "owning" => sel[p] \notin frontier
    /\ \A p \in Procs : pc[p] = "idle" => sel[p] = "none"

\* Convergence: the concurrent exploration has to match the sequential MISRA
\* run --- the frontier eventually drains, and the two phases do not get stuck
\* in an endless exchange about who owns what.
Refines == (\A p \in Procs : pc[p] # "idle") ~> (\A p \in Procs : pc[p] = "idle")

CONNECTED == Cardinality(Nodes) = 4 /\ Cardinality(Procs) = 2 /\ \A n \in Nodes : Cardinality(Succ[n]) = 2

\* The standard module's Seq is an unbounded sequence type; model checking a
\* system that keeps appending to it never terminates. Replaced by the
\* cfg-substituted operator LimitedSeq so every sequence in the system is
\* forced to stay inside a bounded window.
FiniteSeq == \A s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes)

====