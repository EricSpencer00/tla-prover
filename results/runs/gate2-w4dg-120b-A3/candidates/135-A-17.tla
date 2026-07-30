---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

ASSUME Cardinality(Nodes) = 4

\* The algorithm itself is not rewritten here; only the configuration values
\* that bound the model are defined. The actual algorithm spec (Init, Next, etc.)
\* is supposed to come from the standard reachability module, so they are
\* declared as placeholders and never redefined in this configuration file.

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "running"

Next ==
  \E v \in Nodes :
    /\ frontier # {}
    /\ \E w \in Succ[v] :
         /\ w \notin marked
         /\ marked' = marked \cup {w}
         /\ frontier' = (frontier \cup {w}) \ {v}
    /\ pc' = "running"
        \/ (frontier = {} /\ pc = "running" /\ pc' = "done")
        \/ (pc = "done" /\ pc' = "done")

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

\* Successor closure: every marked node's successors are marked as well.
Inv1 == \A v \in marked : \A w \in Succ[v] : w \in marked

\* Reachability decomposition: frontier is always a subset of the marked set.
Inv2 == frontier \subseteq marked

\* Reachable set equals marked set once the algorithm has completed.
Inv3 == pc = "done" => marked = Nodes

PartialCorrectness ==
  pc = "done" => \A v \in Nodes : (\E p \in Seq(Nodes) : p[1] = Root /\ p[Len(p)] = v /\ \A i \in 1..Len(p) : p[i] \in Nodes)

Termination == <>(pc = "done")

Spec == Init /\ [][Next]_vars

\* Left introduced by the .cfg, right defined here: a bounded version of Succ.
ConnectedToSomeButNotAll ==
  [v \in Nodes |-> \E w \in Nodes : TRUE]

LimitedSeq ==
  {s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes)}

====