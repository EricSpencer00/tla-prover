---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

(* ----------------------------------------------------------------------
   Bounded sequence operator: only sequences whose length does not exceed
   the number of nodes are kept, making the state space finite.
   ---------------------------------------------------------------------- *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* ----------------------------------------------------------------------
   Operator that will be substituted for the generic successor relation.
   Here it simply returns the concrete successor set given by the constant
   Succ.  The name is required by the .cfg file.
   ---------------------------------------------------------------------- *)
ConnectedToSomeButNotAll(n) == Succ[n]

(* ----------------------------------------------------------------------
   Set of nodes reachable from Root via a bounded path (using the
   limited sequence operator).
   ---------------------------------------------------------------------- *)
ReachableSet ==
  { n \in Nodes :
      \E s \in LimitedSeq(Nodes) :
        /\ Len(s) >= 1
        /\ s[1] = Root
        /\ s[Len(s)] = n
        /\ \A i \in 1..Len(s)-1 :
            s[i+1] \in ConnectedToSomeButNotAll(s[i])
  }

VARIABLES marked, frontier, pc

(* ----------------------------------------------------------------------
   Initial state: only the root is in the frontier, nothing is marked,
   program counter starts at 0.
   ---------------------------------------------------------------------- *)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = 0

(* ----------------------------------------------------------------------
   One step of the algorithm: pick a node from the frontier, mark it,
   and add its successors (that are not already marked) to the frontier.
   ---------------------------------------------------------------------- *)
Expand ==
  /\ frontier # {}
  /\ \E n \in frontier :
        LET newSucc == ConnectedToSomeButNotAll(n) IN
        /\ marked'   = marked \cup {n}
        /\ frontier' = (frontier \ {n}) \cup (newSucc \ marked)
  /\ pc' = pc + 1

(* ----------------------------------------------------------------------
   Stuttering step when the frontier is empty (algorithm has finished).
   ---------------------------------------------------------------------- *)
Done ==
  /\ frontier = {}
  /\ UNCHANGED <<marked, frontier>>
  /\ pc' = pc

Next ==
  \/ Expand
  \/ Done

(* ----------------------------------------------------------------------
   Full specification: start in Init and repeatedly take Next steps.
   ---------------------------------------------------------------------- *)
Spec ==
  Init /\ [][Next]_<<marked, frontier, pc>>

(* ----------------------------------------------------------------------
   Invariants required by the .cfg file.
   ---------------------------------------------------------------------- *)
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in Nat

Inv1 ==
  /\ \A n \in marked :
        ConnectedToSomeButNotAll(n) \subseteq marked \/ frontier

Inv2 ==
  /\ frontier \subseteq Nodes \ marked

Inv3 ==
  /\ marked = ReachableSet

PartialCorrectness ==
  /\ frontier = {} => marked = ReachableSet

(* ----------------------------------------------------------------------
   Liveness property: the algorithm eventually reaches a state with an
   empty frontier (termination).
   ---------------------------------------------------------------------- *)
Termination ==
  <> (frontier = {})

====