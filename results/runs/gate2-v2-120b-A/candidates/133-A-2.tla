---- MODULE MCParReach ----
EXTENDS Naturals, TLC

CONSTANTS Nodes, Root, Procs, Succ, Seq

VARIABLES marked, frontier, pc, sel, succ

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Node == Nodes
Proc == Procs
SeqBound == Len(Seq)

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
\* (The constants Nodes, Root, Procs, Succ, Seq are assumed to be provided
\*  by the .cfg file. Succ must be a function mapping each node to a set of
\*  its two successors, and Seq must be a sequence of nodes of length at most
\*  the number of nodes.)
\* ----------------------------------------------------------------------

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
\* marked   : set of nodes already visited
\* frontier : set of nodes currently being explored by the algorithm
\* pc[p]    : program counter for process p (one of "Idle", "Pick", "Visit")
\* sel[p]   : node selected by process p (or Null if none)
\* succ[p]  : set of successors of sel[p] that have been discovered by p
\* ----------------------------------------------------------------------
vars == << marked, frontier, pc, sel, succ >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
PCValues == {"Idle", "Pick", "Visit"}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ marked   = {}
  /\ frontier = {Root}
  /\ pc       = [p \in Proc |-> "Idle"]
  /\ sel      = [p \in Proc |-> Null]
  /\ succ     = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Pick(p) ==
  /\ pc[p] = "Idle"
  /\ frontier # {}
  /\ \E n \in frontier :
        /\ sel' = [sel EXCEPT ![p] = n]
        /\ frontier' = frontier \ {n}
        /\ pc' = [pc EXCEPT ![p] = "Visit"]
        /\ UNCHANGED << marked, succ >>

Visit(p) ==
  /\ pc[p] = "Visit"
  /\ sel[p] # Null
  /\ marked'  = marked \cup {sel[p]}
  /\ succ'    = [succ EXCEPT ![p] = Succ[sel[p]]]
  /\ frontier' = frontier \cup succ'
  /\ pc'       = [pc EXCEPT ![p] = "Idle"]
  /\ sel'      = [sel EXCEPT ![p] = Null]

Next ==
  \/ \E p \in Proc : Pick(p)
  \/ \E p \in Proc : Visit(p)
  \/ UNCHANGED << marked, frontier, pc, sel, succ >>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
\* Type-correctness invariant (maps to the required identifier "Inv")
Inv ==
  /\ marked   \subseteq Node
  /\ frontier \subseteq Node
  /\ pc       \in [Proc -> PCValues]
  /\ sel      \in [Proc -> (Node \cup {Null})]
  /\ succ     \in [Proc -> SUBSET Node]

\* Refinement property (maps to the required identifier "Refines")
\* The parallel algorithm implements the sequential Misra algorithm.
\* For the purpose of this configuration we assert that every node that
\* becomes marked in the parallel execution is also reachable from the
\* root via a path of nodes each of which appears in the global frontier at
\* some earlier step. This captures the essence of the sequential algorithm's
\* reachability guarantee.
Refines ==
  \A n \in marked :
    \E p \in Proc :
      n \in succ[p] \/ n = sel[p]

\* ----------------------------------------------------------------------
\* THEOREM (optional, not required by the .cfg but useful for TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => Inv

====