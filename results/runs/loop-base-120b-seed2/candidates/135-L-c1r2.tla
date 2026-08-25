---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root

(*-----------------------------------------------------------------
  Bounded sequence operator used to replace the infinite Seq.
-----------------------------------------------------------------*)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(*-----------------------------------------------------------------
  Concrete successor function.  The cfg will replace any occurrence
  of Succ with ConnectedToSomeButNotAll, so we define the latter
  explicitly.
-----------------------------------------------------------------*)
ConnectedToSomeButNotAll(n) ==
  CASE n = "n0" -> {"n1", "n2"}
  [] n = "n1" -> {"n2", "n3"}
  [] n = "n2" -> {"n0", "n3"}
  [] n = "n3" -> {"n0", "n1"}
  [] OTHER     -> {}

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Initial state: only the root is in the frontier, nothing is marked.
-----------------------------------------------------------------*)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Running"

(*-----------------------------------------------------------------
  One step of the algorithm: pick a node from the frontier,
  add its successors to the marked set, and update the frontier.
-----------------------------------------------------------------*)
Step ==
  /\ frontier # {}
  /\ \E n \in frontier :
        /\ marked'    = marked \cup ConnectedToSomeButNotAll(n)
        /\ frontier'  = (frontier \ {n}) \cup (ConnectedToSomeButNotAll(n) \ marked)
        /\ pc'        = "Running"

(*-----------------------------------------------------------------
  Termination step: when the frontier is empty, the process stops.
-----------------------------------------------------------------*)
Done ==
  /\ frontier = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<marked, frontier>>

Next == Step \/ Done

Spec == Init /\ [][Next]_vars

(*-----------------------------------------------------------------
  Type correctness invariant.
-----------------------------------------------------------------*)
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"Running", "Done"}

(*-----------------------------------------------------------------
  Invariant 1: successor closure – every marked node's successors
                are also marked.
-----------------------------------------------------------------*)
Inv1 ==
  \A n \in marked : ConnectedToSomeButNotAll(n) \subseteq marked

(*-----------------------------------------------------------------
  Invariant 2: frontier consists only of unmarked nodes.
-----------------------------------------------------------------*)
Inv2 ==
  /\ frontier \subseteq Nodes \ marked
  /\ \A n \in frontier : ConnectedToSomeButNotAll(n) \subseteq Nodes

(*-----------------------------------------------------------------
  Reachable set defined via bounded sequences.
-----------------------------------------------------------------*)
ReachableSet ==
  { n \in Nodes :
        \E seq \in LimitedSeq(Nodes) :
          /\ Len(seq) >= 1
          /\ seq[1] = Root
          /\ seq[Len(seq)] = n
          /\ \A i \in 1 .. Len(seq)-1 :
                seq[i+1] \in ConnectedToSomeButNotAll(seq[i]) }

(*-----------------------------------------------------------------
  Invariant 3: marked set equals the set of nodes reachable from Root.
-----------------------------------------------------------------*)
Inv3 == marked = ReachableSet

(*-----------------------------------------------------------------
  Partial correctness: when the algorithm terminates, the marked set
  is exactly the reachable set.
-----------------------------------------------------------------*)
PartialCorrectness ==
  (pc = "Done") => (marked = ReachableSet)

(*-----------------------------------------------------------------
  Liveness property: the algorithm eventually reaches the Done state.
-----------------------------------------------------------------*)
Termination == <> (pc = "Done")

====