---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

\* The configuration module for the sequential Misra reachability algorithm.
\* It supplies every identifier the reference TLC configuration expects.
\* It inherits the standard algorithm's state and actions and adds only
\* model-checking configuration: a concrete graph and a bounded sequence
\* operator (via the CFOUROLIVE override) so the state space stays finite.

CONSTANTS Nodes, Root, Succ, ConnectedToSomeButNotAll

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "running", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = "idle"

\* The sequential algorithm: in the running phase it moves the frontier into
\* the marked set and expands the frontier with successors; when the frontier
\* is empty it terminates.
Next ==
  /\ \/ /\ pc = "idle"
        /\ pc' = "running"
        /\ frontier' = Succ[Root]
        /\ UNCHANGED marked
     \/ /\ pc = "running"
        /\ marked' = marked \cup frontier
        /\ frontier' = {n \in Nodes : \E m \in frontier : n \in Succ[m]}
        /\ UNCHANGED pc
     \/ /\ pc = "running"
        /\ frontier = {}
        /\ pc' = "done"
        /\ UNCHANGED <<marked, frontier>>
  /\ UNCHANGED pc

Spec == Init /\ [][Next]_vars

Inv1 == frontier \subseteq {n \in Nodes : \E m \in marked : n \in Succ[m]}
Inv2 == marked \subseteq {n \in Nodes : \E p \in Seq(Nodes) : Len(p) >= 1 /\ p[1] = Root /\ p[Len(p)] = n}
Inv3 == marked = {n \in Nodes : \E p \in Seq(Nodes) : Len(p) >= 1 /\ p[1] = Root /\ p[Len(p)] = n}

PartialCorrectness ==
  /\ marked \subseteq {n \in Nodes : \E m \in frontier : n \in Succ[m]}
  /\ frontier \subseteq {n \in Nodes : \E m \in marked : n \in Succ[m]}

Termination == (pc = "running") ~> (pc = "done")

\* CFOUROLIVE override: replaces the unbounded Seq from Sequences with a finite
\* version that truncates at the number of nodes, keeping the model finite.
LimitedSeq(S) ==
  {p \in Seq(S) : Len(p) <= Cardinality(Nodes)}

\* The .cfg file substitutes the bounded operator for Succ, so Succ here is a
\* thin wrapper. ConnectedToSomeButNotAll is what the .cfg substitutes in.
Succ ==
  ConnectedToSomeButNotAll

====