---- MODULE MCParReach ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\* The overridden operator ConnectedToSomeButNotAll is what the .cfg substitutes in
\* for the original Succ, but Succ itself is a declared constant here that the
\* configuration also sets -- both must appear, exactly as written.
ConnectedToSomeButNotAll == { y \in Nodes : y # Root }

\* The overridden operator LimitedSeq replaces the infinite SEQ operator; it
\* must be defined without redefining the name Seq, which stays from the
\* Sequences module.
LimitedSeq(S) == CHOOSE s \in [1..Len(S) -> S] : TRUE

VARIABLES marked, frontier, pc, sel, succ

vars == <<marked, frontier, pc, sel, succ>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "work"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succ \in [Nodes -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succ = [n \in Nodes |-> ConnectedToSomeButNotAll]

Select(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in marked
  /\ pc' = [pc EXCEPT ![p] = "work"]
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ UNCHANGED <<marked, frontier, succ>>

Explore(p) ==
  /\ pc[p] = "work"
  /\ sel[p] \notin frontier
  /\ frontier' = frontier \cup {sel[p]}
  /\ succ' = [succ EXCEPT ![sel[p]] = succ[sel[p]]]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ UNCHANGED marked

Mark(n) ==
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ marked' = marked \cup {n}
  /\ UNCHANGED <<pc, sel, succ>>

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs : Explore(p)
  \/ \E n \in Nodes : Mark(n)

Spec == Init /\ [][Next]_vars

\* Safety property: every marked node is reachable from the root via the
\* bounded successor relation (bounded because succ is a finite set per node).
Inv == \A n \in Nodes : n \in marked => \E s \in LimitedSeq(Nodes) :
  /\ Len(s) >= 1
  /\ s[1] = Root
  /\ s[Len(s)] = n
  /\ \A i \in 1..(Len(s) - 1) : s[i+1] \in succ[s[i]]

Refines == Inv

====