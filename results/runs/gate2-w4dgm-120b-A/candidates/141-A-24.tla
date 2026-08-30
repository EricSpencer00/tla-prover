---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

\* Misra's variant: visited and frontier may overlap, which is what makes
\* the loop amenable to parallel execution. Still sequential here.
Variables marked, frontier, pc

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "terminated"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

\* Two cases on one nondeterministic pick from the frontier: mark and
\* expand, or clean up a node that was already marked.
Explore ==
    /\ pc = "running"
    /\ frontier # {}
    /\ \E n \in frontier :
         IF n \notin marked
         THEN /\ marked' = marked \cup {n}
              /\ frontier' = frontier \cup Succ[n]
         ELSE /\ marked' = marked
              /\ frontier' = frontier \ {n}
    /\ pc' = IF frontier = {} THEN "terminated" ELSE "running"

Spec == Init /\ [][Explore]_<<marked, frontier, pc>>

\* Relies on graph reachability being closed under union: nodes reachable
\* from the union of marked and frontier are exactly marked plus
\* whatever the frontier can still reach.
Nxt == UNION { Succ[n] : n \in Nodes }

Inv1 == \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 == (ReachableFrom(Nodes, marked) \cup ReachableFrom(Nodes, frontier))
            = ReachableFrom(Nodes, marked \cup frontier)

Inv3 == ReachableFrom(Nodes, {Root}) = (marked \cup ReachableFrom(Nodes, frontier))

PartialCorrectness == pc = "terminated" => marked = ReachableFrom(Nodes, {Root})

\* Termination is only guaranteed on a finite reachable set; the bounded
\* frontier keeps the reachable set finite in that case.
Termination == (Cardinality(ReachableFrom(Nodes, {Root})) < Cardinality(Nodes))
                  ~> (frontier = {})

\* The cfg substitutes in Succ and the (finite) Seq operator, so define
\* nothing else for them here.
====