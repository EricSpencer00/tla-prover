---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*--------------------------------------------------------------------
  Constants (to be instantiated in the .cfg)
--------------------------------------------------------------------*)
CONSTANTS
    Nodes,   \* The finite set of graph nodes
    Root,    \* The distinguished start node
    Succ,    \* Function mapping each node to exactly two successors
    Seq      \* A finite set of sequences (paths) used in the definition of Reachable

(*--------------------------------------------------------------------
  Type definitions
--------------------------------------------------------------------*)
Node == Nodes
Edges == [node \in Nodes |-> Succ[node]]

(*--------------------------------------------------------------------
  Derived constants for convenience
--------------------------------------------------------------------*)
NodeSet == Nodes
AllSeqs == { s \in Seq : Len(s) <= Cardinality(Nodes) }

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES
    marked,   \* Set of nodes already discovered
    frontier, \* Set of nodes discovered but not yet expanded
    pc        \* Program counter (captures which step of the algorithm)

(*--------------------------------------------------------------------
  Initialization
--------------------------------------------------------------------*)
Init ==
    /\ marked   = {}
    /\ frontier = {Root}
    /\ pc       = "Loop"

(*--------------------------------------------------------------------
  Helper: Successor closure for a set of nodes
--------------------------------------------------------------------*)
SuccSet(S) == UNION { Succ[n] : n \in S }

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
Loop ==
    /\ pc = "Loop"
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

Explore ==
    /\ pc = "Loop"
    /\ frontier # {}
    /\ \E n \in frontier :
         /\ marked'   = marked \cup {n}
         /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked')
         /\ pc'       = "Loop"
    /\ UNCHANGED <<pc>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<marked, frontier, pc>>

Next ==
    \/ Loop
    \/ Explore
    \/ Done

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*--------------------------------------------------------------------
  Safety invariants
--------------------------------------------------------------------*)
TypeOK ==
    /\ marked   \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Loop", "Done"}

Inv1 ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ marked \cup frontier \subseteq Nodes

Inv2 ==
    /\ frontier \subseteq SuccSet(marked)

Inv3 ==
    /\ marked = { n \in Nodes :
           \E s \in AllSeqs :
               /\ Len(s) >= 1
               /\ s[1] = Root
               /\ s[Len(s)] = n
               /\ \A i \in 1..Len(s)-1 : s[i+1] \in Succ[s[i]] } }

PartialCorrectness ==
    /\ pc = "Done"
    /\ marked = Nodes

(*--------------------------------------------------------------------
  Liveness property (termination)
--------------------------------------------------------------------*)
Termination == <> (pc = "Done")

=============================================================================