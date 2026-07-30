---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

\* Succ is an operator giving the successors of a node; it is overridden in the
\* .cfg (e.g. with ConnectedToSomeButNotAll), so we define it here but never
\* use an explicit body -- the .cfg supplies the meaning.
Succ(n) == {}

VARIABLES visited, frontier, pc

vars == << visited, frontier, pc >>

TypeOK ==
  /\ visited \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "terminated"}

Init ==
  /\ visited = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* The loop picks any frontier node and either marks it (merging its successors
\* into the frontier without removing it) or drops it once already marked.
Step ==
  /\ pc = "running"
  /\ frontier # {}
  /\ \E n \in frontier :
       /\ IF n \notin visited
            THEN /\ visited' = visited \cup {n}
                 /\ frontier' = frontier \cup Succ(n)
            ELSE /\ visited' = visited
                 /\ frontier' = frontier \ {n}
  /\ pc' = "running"

AllDone ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "terminated"
  /\ UNCHANGED << visited, frontier >>

Next == Step \/ AllDone

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Step)

\* Every successor of a visited node is either already visited or in the
\* frontier (never lost by the merge-and-don't-remove step).
Inv1 ==
  \A n \in visited : Succ(n) \subseteq (visited \cup frontier)

\* The visited set plus the reachable set from the frontier is upward-closed
\* under union with the frontier itself (a reachability consistency check).
Inv2 ==
  ReachableFrom(visited \cup frontier) = visited \cup ReachableFrom(frontier)

\* The reachable set from the root is partitioned exactly between what is
\* visited and what remains reachable only via the frontier.
Inv3 ==
  ReachableFrom({Root}) = visited \cup ReachableFrom(frontier)

PartialCorrectness ==
  (pc = "terminated") => (visited = ReachableFrom({Root}))

Termination ==
  (\E N \in Nat : Cardinality(ReachableFrom({Root})) = N) ~> (pc = "terminated")

\* ReachableFrom is defined in terms of the (possibly overridden) Succ operator,
\* giving the ordinary reflexive-transitive closure of the graph.
ReachableFrom(X) ==
  LET nxt[T \in SUBSET Nodes] ==
        {n \in Nodes : (\E t \in T : n \in Succ(t))}
  IN LET R ==
       {n \in Nodes :
          \E f \in [Nat -> Nodes] :
            /\ f[0] \in X
            /\ \A i \in Nat : f[i+1] \in nxt({f[i]})
            /\ \E j \in Nat : f[j] = n}
     IN R \cup X

\* The .cfg overrides Seq from Sequences with a finite version (LimitedSeq); we
\* keep the EXTENDS and never declare Seq, so the substitution is legal.
LimitedSeq == {}

====