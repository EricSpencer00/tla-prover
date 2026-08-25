---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

(*--------------------------------------------------------------------
  Concrete graph definition: each node has exactly two successors.
  The configuration replaces Succ with this operator.
--------------------------------------------------------------------*)
ConnectedToSomeButNotAll == 
  [n \in Nodes |-> 
    { ((n) % 4) + 1 , ((n + 1) % 4) + 1 } ]

(*--------------------------------------------------------------------
  Bounded sequence operator used in place of the infinite Seq.
--------------------------------------------------------------------*)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

VARIABLES marked, frontier, pc

(*--------------------------------------------------------------------
  Initial state: only the root is in the frontier, nothing is marked.
--------------------------------------------------------------------*)
Init == 
  /\ marked   = {}
  /\ frontier = {Root}
  /\ pc       = "Run"

(*--------------------------------------------------------------------
  One step of the reachability algorithm.
--------------------------------------------------------------------*)
AddFrontier == 
  /\ pc = "Run"
  /\ \E n \in frontier :
        LET succs == Succ[n] IN
        /\ marked'   = marked \cup {n}
        /\ frontier' = (frontier \ {n}) \cup (succs \ marked)
        /\ pc'       = "Run"
        /\ UNCHANGED <<>>

Done == 
  /\ pc = "Run"
  /\ frontier = {}
  /\ pc'       = "Done"
  /\ UNCHANGED <<marked, frontier>>

Next == AddFrontier \/ Done

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*--------------------------------------------------------------------
  Type correctness invariant
--------------------------------------------------------------------*)
TypeOK == 
  /\ marked   \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"Run", "Done"}

(*--------------------------------------------------------------------
  Invariant 1: successor closure
--------------------------------------------------------------------*)
Inv1 == 
  \A n \in marked : Succ[n] \subseteq marked \cup frontier

(*--------------------------------------------------------------------
  Invariant 2: all variables stay within the node universe
--------------------------------------------------------------------*)
Inv2 == 
  /\ marked   \subseteq Nodes
  /\ frontier \subseteq Nodes

(*--------------------------------------------------------------------
  Invariant 3: marked set equals the set of nodes reachable via
  bounded sequences from the root.
--------------------------------------------------------------------*)
ReachableSet == 
  { n \in Nodes :
      \E seq \in LimitedSeq(Nodes) :
        /\ Len(seq) >= 1
        /\ seq[1] = Root
        /\ seq[Len(seq)] = n
        /\ \A i \in 1..Len(seq)-1 : seq[i+1] \in Succ[seq[i]] }

Inv3 == marked = ReachableSet

(*--------------------------------------------------------------------
  Partial correctness: when the algorithm finishes, all nodes are marked.
--------------------------------------------------------------------*)
PartialCorrectness == 
  (pc = "Done") => (marked = Nodes)

(*--------------------------------------------------------------------
  Liveness property: the algorithm eventually terminates.
--------------------------------------------------------------------*)
Termination == <> (pc = "Done")

====