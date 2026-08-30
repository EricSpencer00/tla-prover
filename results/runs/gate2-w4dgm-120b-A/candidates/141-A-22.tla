---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

\* Nodes is the finite node universe; Succ is a graph edge function that the
\* cfg file substitutes in as a bounded version of the (possibly infinite)
\* successor relation. ReachableNodes is the standard inductive closure.
\* Misra's twist is that Marked and Frontier are allowed to overlap.
CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* Pick any frontier node; add its successors to the frontier when marking it,
\* or retire it from the frontier once already marked. Marked and frontier
\* overlap freely -- that is the point, not the bug.
Step ==
  /\ frontier # {}
  /\ \E n \in frontier :
       \/ IF n \notin marked
            THEN /\ marked' = marked \cup {n}
                 /\ frontier' = frontier \cup Succ[n]
            ELSE /\ marked' = marked
                 /\ frontier' = frontier \ {n}
  /\ pc' = "running"

Done ==
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ Step
  \/ Done

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* Every successor of a marked node is either already marked or still
\* waiting in the frontier; nothing is lost in transit.
Inv1 ==
  \A n \in marked : \A m \in Succ[n] : m \in marked \/ m \in frontier

\* Marked plus the successors of the frontier is closed under Succ: no
\* edge from that set points outside it.
Inv2 ==
  \A n \in (marked \cup {m \in Nodes : \E o \in frontier : m \in Succ[o]}) :
    \A c \in Succ[n] : c \in (marked \cup {m \in Nodes : \E o \in frontier : m \in Succ[o]})

\* Reachable nodes are exactly the marked nodes plus whatever the current
\* frontier can still reach.
Inv3 ==
  ReachableFrom(Nodes, Root) = marked \cup ReachableFrom(Nodes, frontier)

PartialCorrectness == Inv1 /\ Inv2 /\ Inv3

\* Fairness: the loop cannot stall forever at a non-empty frontier.
Termination == (frontier # {}) ~> (frontier = {})

\* ReachableFrom is the standard inductive-closure definition over a node
\* set and a start set, included here so the cfg's substitution of Succ
\* has a concrete target inside the module.
ReachableFrom(V, S) ==
  LET R == \{ x \in V :
                \E f \in [1 .. Cardinality(V) -> V] :
                  \E k \in 1 .. Cardinality(V) :
                    /\ \A i \in 1 .. k : f[i] \in S
                    /\ \A i \in 1 .. (k - 1) : f[i + 1] \in Succ[f[i]]
                    /\ f[k] = x \} IN R

\* FiniteSeq is the cfg file's bounded replacement for the built-in
\* Sequences.Seq operator; the module only needs to name it, so it may
\* be a trivial stub -- the cfg substitution provides the real one.
LimitedSeq(S) == CHOOSE s \in Seq(S) : TRUE

=============================================================================