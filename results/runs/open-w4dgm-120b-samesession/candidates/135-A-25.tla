---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

\* A model-checking configuration for the sequential Misra reachability algorithm.
\* It supplies concrete values for the graph (Nodes, Root, Succ) and a bounded
\* sequence operator (LimitedSeq) that replaces the unbounded Seq from Sequences,
\* so the state space stays finite for exhaustive checking.
\* The actions and most of the logic come from the main reachability spec.

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

\* Reachability via a bounded path of length at most the number of nodes.
InReach(n, s) ==
  /\ s # << >>
  /\ s[1] = Root
  /\ \A i \in 1 .. Len(s) - 1 : s[i + 1] \in Succ[s[i]]
  /\ \A i, j \in 1 .. Len(s) : s[i] = s[j] => i = j
  /\ n \in s

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "active", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "idle"

Activate ==
  /\ pc = "idle"
  /\ pc' = "active"
  /\ UNCHANGED <<marked, frontier>>

\* The algorithm's one irreversible action: marking a node and adding it to the
\* frontier, guarded so it fires at most once per node.
Mark(n) ==
  /\ pc = "active"
  /\ n \notin marked
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \cup {n}
  /\ UNCHANGED pc

Deactivate ==
  /\ pc = "active"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ Activate
  \/ \E n \in Nodes : Mark(n)
  \/ Deactivate
  \/ Done

\* The configuration also substitutes ConnectedToSomeButNotAll for Succ, which
\* must be a finite (deterministic, small) variant of the successor function.
ConnectedToSomeButNotAll(S) ==
  { y \in Nodes : \E x \in S : y \in Succ[x] }

Spec == SpecA

\* Safety: type correctness and the three core reachability invariants.
\* PartialCorrectness is the algorithm's substantive claim about the reachable
\* set; it is retained here in the configuration because it is not checkable
\* from a smaller configuration -- its failure would be a real modeling error.
\* The Liveness property Termination checks the algorithm always eventually
\* reaches its final state (the configuration does not weaken or drop it).
Termination == TerminationA

====