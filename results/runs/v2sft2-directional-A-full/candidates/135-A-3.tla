---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

(* ----------------------------------------------------------------------
   CONSTANTS
   ---------------------------------------------------------------------- *)
CONSTANTS Nodes, Root, Succ, Seq

(* ----------------------------------------------------------------------
   Derived definitions
   ---------------------------------------------------------------------- *)
\* The type of a node is the set of all node identifiers
Node == [id: Nodes]

\* The type of a successor function: for each node, a set of its successors
SuccType == [n \in Nodes |-> {s \in Nodes: s \in Succ[n]}]

\* A sequence of nodes (path) is simply a list of node identifiers
Path == Seq

\* The tail of a path (if non-empty)
Tail(xs) == IF Len(xs) = 0 THEN {} ELSE SubSeq(xs, 2, Len(xs))

\* A path is finite and consists only of nodes from Nodes
FiniteSeq == [xs \in Seq: \A i \in 1..Len(xs): xs[i] \in Nodes]

\* The length of a path
Len(xs) == Len(xs)

(* ----------------------------------------------------------------------
   Variables (inherited from the algorithm)
   ---------------------------------------------------------------------- *)
VARIABLES Marked, Frontier, pc

(* ----------------------------------------------------------------------
   Type correctness invariant (required)
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ pc \in {"Init", "Scan", "Done"}

(* ----------------------------------------------------------------------
   Initial state (inherited from the algorithm)
   ---------------------------------------------------------------------- *)
Init ==
    /\ Marked = {}
    /\ Frontier = {Root}
    /\ pc = "Init"

(* ----------------------------------------------------------------------
   Algorithm actions (inherited from the algorithm)
   ---------------------------------------------------------------------- *)
\* Scan action: move a node from Frontier to Marked and add its successors
Scan ==
    /\ pc = "Scan"
    /\ \E x \in Frontier:
          /\ x \notin Marked
          /\ Marked' = Marked \cup {x}
          /\ Frontier' = (Frontier \ {x}) \cup Succ[x]
          /\ pc' = pc

\* Transition to Done when frontier is empty
Done ==
    /\ pc = "Scan"
    /\ Frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<Marked, Frontier>>

\* Next-state relation
Next ==
    Scan \/ Done

(* ----------------------------------------------------------------------
   Specification (required)
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

(* ----------------------------------------------------------------------
   Algorithm invariants (required)
   ---------------------------------------------------------------------- *)

\* Inv1: All nodes in Marked were reachable via a path from Root
Inv1 ==
    \A x \in Marked: \E p \in Path:
        /\ p[1] = Root
        /\ p[Len(p)] = x
        /\ \A i \in 1..Len(p)-1: p[i+1] \in Succ[p[i]]

\* Inv2: The frontier always contains only successors of marked nodes
Inv2 ==
    Frontier \subseteq \cup_{x \in Marked} Succ[x]

\* Inv3: All nodes in the frontier are distinct from marked nodes
Inv3 ==
    Frontier \cap Marked = {}

\* Partial correctness: when the algorithm terminates, the marked set
\* equals the set of all nodes reachable from Root
PartialCorrectness ==
    pc = "Done" => Marked = \{x \in Nodes: \E p \in Path:
                            /\ p[1] = Root
                            /\ p[Len(p)] = x
                            /\ \A i \in 1..Len(p)-1: p[i+1] \in Succ[p[i]]\}

(* ----------------------------------------------------------------------
   Liveness property (required)
   ---------------------------------------------------------------------- *)
Termination ==
    <><>(pc = "Done")

(* ----------------------------------------------------------------------
   Specification for TLC
   ---------------------------------------------------------------------- *)
THEOREM SpecIsInvariant:
    SPECIFICATION Spec

====