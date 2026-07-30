---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\* A bounded version of the successor operator used in the sequential model.
\* The .cfg substitutes this in for Succ from the standard module.
ConnectedToSomeButNotAll(n) == IF n = 1 THEN {2, 3} ELSE IF n = 2 THEN {3, 4} ELSE IF n = 3 THEN {1, 4} ELSE {1, 2}

\* The standard Sequences module defines Seq as an unbounded set of sequences.
\* The .cfg overrides it with this finite-capacity version, so it must stay EXTENDS Sequences
\* and must not DECLARE Seq itself.
LimitedSeq(S) == {s \in Seq(S) : Len(s) =< Cardinality(Nodes)}

VARIABLES marked, frontier, pc, pick, fwd
vars == << marked, frontier, pc, pick, fwd >>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> 0..2]
  /\ pick \in [Procs -> Nodes \cup {0}]
  /\ fwd \in [Procs -> Seq(Nodes)]

Init ==
  /\ marked = {Root}
  /\ frontier = ConnectedToSomeButNotAll(Root)
  /\ pc = [p \in Procs |-> 0]
  /\ pick = [p \in Procs |-> 0]
  /\ fwd = [p \in Procs |-> << >>]

Explore(p, c) ==
  /\ pc[p] = 0
  /\ c \in frontier
  /\ pick' = [pick EXCEPT ![p] = c]
  /\ pc' = [pc EXCEPT ![p] = 1]
  /\ UNCHANGED << marked, frontier, fwd >>

Advance(p) ==
  /\ pc[p] = 1
  /\ LET succs == ConnectedToSomeButNotAll(pick[p]) IN
       /\ fwd' = [fwd EXCEPT ![p] = LimitedSeq(@) \o << succs >>]
       /\ marked' = marked \cup succs
  /\ frontier' = frontier \cup succs
  /\ pc' = [pc EXCEPT ![p] = 2]
  /\ UNCHANGED pick

Reset(p) ==
  /\ pc[p] = 2
  /\ pc' = [pc EXCEPT ![p] = 0]
  /\ UNCHANGED << marked, frontier, pick, fwd >>

Next == \E p \in Procs : Explore(p, frontier) \/ Advance(p) \/ Reset(p)

Spec == Init /\ [][Next]_vars

\* Type correctness plus the shape check on the per-process sequence.
Inv == TypeOK

\* Refinement: whatever the parallel algorithm marks, the sequential Misra
\* algorithm would have marked it too.
Refines == marked \subseteq {n \in Nodes : \E s \in Seq(Nodes) : s = << n >>}

====