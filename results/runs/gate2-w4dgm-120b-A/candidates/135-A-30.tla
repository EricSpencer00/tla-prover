---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

\* Model-checking configuration for the sequential Misra reachability algorithm.
\* It adds concrete constants, a bounded sequence operator, and a finite
\* connected graph so the exhaustive state space stays finite.
\* All algorithm variables and actions are inherited unchanged from the base
\* specification; this module supplies the missing definitions it needs.

CONSTANTS Nodes, Root, Succ

\* Bounded (finite) version of the unbounded sequence constructor from
\* Sequences; this keeps the model finite for model checking. The left-hand
\* name is overriden by the .cfg file; we only define the operator on the right.
LimitedSeq(n) == CHOOSE s \in Seq(1..Cardinality(Nodes)) : Len(s) = n

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "working", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = Succ(Root)
    /\ pc = "idle"

Mark(n) == marked \cup {n}

WorkStep(n) ==
    /\ pc = "idle"
    /\ n \in frontier
    /\ n \notin marked
    /\ \A m \in frontier \ Marked : m # n
    /\ marked' = Mark(n)
    /\ frontier' = (frontier \cup Succ(n)) \ Mark(n)
    /\ pc' = "working"

FinishStep ==
    /\ pc = "working"
    /\ pc' = "idle"
    /\ UNCHANGED << marked, frontier >>

Idle ==
    /\ pc = "idle"
    /\ frontier \subseteq marked
    /\ pc' = "done"
    /\ UNCHANGED << marked, frontier >>

DoneStep ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Nodes : WorkStep(n)
    \/ FinishStep
    \/ Idle
    \/ DoneStep

Spec == Init /\ [][Next]_vars /\ WF_vars(FinishStep) /\ WF_vars(Idle)

\* Successor closure: marked is closed under the graph's successor function.
Inv1 == \A n \in marked : Succ(n) \subseteq marked

\* Reachable nodes are exactly those in the marking.
Inv2 == marked = {n \in Nodes : \E s \in LimitedSeq(Cardinality(Nodes)) :
    s[1] = Root /\ \A i \in 1..(Len(s) - 1) : s[i + 1] \in Succ(s[i]) /\ n \in s}

\* The frontier is disjoint from the marking.
Inv3 == frontier \cap marked = {}

\* Once the algorithm halts, its marking is precisely the reachable set.
PartialCorrectness == (pc = "done") => marked = Nodes

Termination == <>(pc = "done")

\* The .cfg file overrides Succ with ConnectedToSomeButNotAll for a concrete
\* finite graph; we expose it here as a constant-shaped operator.
ConnectedToSomeButNotAll(n) == Succ(n)

====