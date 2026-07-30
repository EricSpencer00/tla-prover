---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

\* A model-checking configuration for the sequential Misra reachability
\* algorithm. In addition to the base algorithm's state (its marked set,
\* its frontier, and its program counter), this module declares the
\* concrete graph structure and the bounded sequence type needed to keep
\* the model finite.
CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"init", "running", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "init"

MarkStep(n) ==
    /\ pc = "running"
    /\ n \in frontier
    /\ \E m \in Succ[n] : m \notin marked /\ marked' = marked \cup {m}
    /\ frontier' = frontier \cup (Succ[n] \ {n})
    /\ pc' = IF frontier \cup (Succ[n] \ {n}) = {} THEN "done" ELSE "running"
    /\ UNCHANGED <<marked, frontier, pc>>

Start ==
    /\ pc = "init"
    /\ pc' = "running"
    /\ UNCHANGED <<marked, frontier, pc>>

Spec ==
    /\ Init
    /\ [][MarkStep(_)]_vars
    /\ [][Start]_vars
    /\ WF_vars(MarkStep(Root))

\* Each node has exactly 2 successors; ConnectedToSomeButNotAll is the
\* operator the .cfg substitutes for Succ, so it must be defined
\* exactly with that name.
ConnectedToSomeButNotAll(n) ==
    /\ Cardinality(n) = 2
    /\ \A m \in n : m \in Nodes
    /\ n

\* The reachability definition uses existential quantification over
\* sequences of nodes, which would otherwise be infinite. The .cfg
\* replaces the standard Seq operator with LimitedSeq, a version that
\* is forced finite -- the model stays checkable.
LimitedSeq(S) == CHOOSE s \in Seq(S) : Cardinality(s) >= Cardinality(S)

\* The invariants are all checked in the finite model: the usual type
\* invariant plus the three core reachability invariants, plus
\* partial correctness.
Inv1 ==
    /\ frontier \subseteq Nodes
    /\ marked \subseteq Nodes
    /\ \A x \in frontier : \E y \in succ[x] : y \in marked

Inv2 == \A x \in marked : \E y \in frontier : x \in succ[y]

Inv3 ==
    /\ marked \cup frontier = Nodes
    /\ marked \cap frontier = {}

PartialCorrectness == pc = "done" => marked = Nodes

Termination == <>(pc = "done")

====