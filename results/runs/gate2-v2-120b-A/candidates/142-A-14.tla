---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants required by the configuration
\* ----------------------------------------------------------------------
CONSTANTS Nodes, Root

\* ----------------------------------------------------------------------
\* State variables (inherited from the sequential reachability algorithm)
\* ----------------------------------------------------------------------
VARIABLES Marked, Frontier, pc

\* ----------------------------------------------------------------------
\* Type correctness invariant (part of Invariant1)
\* ----------------------------------------------------------------------
TypeOK == 
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ pc \in {"init", "step", "done"}

\* ----------------------------------------------------------------------
\* Reachability definitions
\* ----------------------------------------------------------------------
\* Immediate successors (edges) are assumed to be given by a constant Edges.
\* Edges : SUBSET [src : Nodes, dst : Nodes]
\* For the purpose of this proof module we keep Edges abstract.
CONSTANT Edges

\* Successors of a node
Succ[n \in Nodes] == { e["dst"] : e \in Edges /\ e["src"] = n }

\* The standard ReachableFrom definition (finite graph)
ReachableFrom(S) ==
    LET R == RECURSIVE R(_)
    IN
        R(S) == S \cup UNION { Succ[n] : n \in R(S) }

\* ----------------------------------------------------------------------
\* Initial state (as defined in the algorithm module)
\* ----------------------------------------------------------------------
Init == 
    /\ Marked = {}
    /\ Frontier = {Root}
    /\ pc = "init"

\* ----------------------------------------------------------------------
\* Actions (as defined in the algorithm module)
\* ----------------------------------------------------------------------
Step ==
    /\ pc = "init"
    /\ pc' = "step"
    /\ UNCHANGED <<Marked, Frontier>>

MarkFrontier ==
    /\ pc = "step"
    /\ Marked' = Marked \cup Frontier
    /\ Frontier' = {}
    /\ pc' = "step"
    /\ UNCHANGED Marked

Expand ==
    /\ pc = "step"
    /\ Marked' = Marked
    /\ Frontier' = { n \in Nodes : 
                       \E m \in Marked : n \in Succ[m] /\ n \notin Marked }
    /\ pc' = IF FRONTIER' = {} THEN "done" ELSE "step"
    /\ UNCHANGED Marked

Done ==
    /\ pc = "done"
    /\ UNCHANGED <<Marked, Frontier, pc>>

Next == 
    \/ Step
    \/ MarkFrontier
    \/ Expand
    \/ Done

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

\* ----------------------------------------------------------------------
\* Invariant 1 (inductive): type correctness plus every successor of a 
\* marked node is in Marked or Frontier.
\* ----------------------------------------------------------------------
Inv1 == 
    /\ TypeOK
    /\ \A n \in Marked : Succ[n] \subseteq (Marked \cup Frontier)

\* ----------------------------------------------------------------------
\* Invariant 2: Marked ∪ ReachableFrom(Frontier) = ReachableFrom(Marked ∪ Frontier)
\* (proved from Lemma 1)
\* ----------------------------------------------------------------------
Inv2 == 
    ReachableFrom(Marked \cup Frontier) = Marked \cup ReachableFrom(Frontier)

\* ----------------------------------------------------------------------
\* Invariant 3: ReachableFrom({Root}) = Marked ∪ ReachableFrom(Frontier)
\* (proved from Lemma 2 and Lemma 3)
\* ----------------------------------------------------------------------
Inv3 == 
    ReachableFrom({Root}) = Marked \cup ReachableFrom(Frontier)

\* ----------------------------------------------------------------------
\* Combined invariant list (as required by the .cfg)
\* ----------------------------------------------------------------------
INVARIANTS == <<Inv1, Inv2, Inv3>>

\* ----------------------------------------------------------------------
\* Safety property: partial correctness upon termination
\* ----------------------------------------------------------------------
Safety == 
    pc = "done" => Marked = ReachableFrom({Root})

\* ----------------------------------------------------------------------
\* The .cfg expects a property named PROPERTIES (optional)
\* ----------------------------------------------------------------------
PROPERTIES == Safety

====