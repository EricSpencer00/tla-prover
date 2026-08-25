---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Nodes, Root, Succ

(* ----------------------------------------------------------------------
   Bounded successor relation: each node has exactly two distinct successors.
   ---------------------------------------------------------------------- *)
ConnectedToSomeButNotAll(n) ==
  { m \in Nodes : m # n }   \* all other nodes; the cfg will treat this as Succ

(* Ensure the graph meets the required shape for model checking. *)
ASSUME \A n \in Nodes : Cardinality(ConnectedToSomeButNotAll(n)) = 2

(* ----------------------------------------------------------------------
   Bounded sequences: length at most |Nodes|
   ---------------------------------------------------------------------- *)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

VARIABLES Marked, Frontier, pc

vars == <<Marked, Frontier, pc>>

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "Init"

(* ----------------------------------------------------------------------
   Next-state relation
   ---------------------------------------------------------------------- *)
Next ==
  \/ /\ pc = "Init"
        /\ pc' = "Step"
        /\ UNCHANGED <<Marked, Frontier>>
  \/ /\ pc = "Step"
        /\ \E n \in Frontier :
            LET new == ConnectedToSomeButNotAll(n) \ Marked IN
            /\ Marked'   = Marked \cup {n}
            /\ Frontier' = (Frontier \ {n}) \cup new
            /\ pc'       = IF (Frontier \ {n}) \cup new = {} THEN "Done" ELSE "Step"
  \/ /\ pc = "Done"
        /\ UNCHANGED <<Marked, Frontier, pc>>

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_vars

(* ----------------------------------------------------------------------
   Type correctness invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"Init", "Step", "Done"}

(* ----------------------------------------------------------------------
   Helper: reachable via a bounded path
   ---------------------------------------------------------------------- *)
ReachableViaPath(n) ==
  \E s \in LimitedSeq(Nodes) :
    /\ Len(s) > 0
    /\ s[1] = Root
    /\ s[Len(s)] = n
    /\ \A i \in 1 .. Len(s)-1 :
         s[i+1] \in ConnectedToSomeButNotAll(s[i])

(* ----------------------------------------------------------------------
   Invariant 1: successor closure
   ---------------------------------------------------------------------- *)
Inv1 ==
  \A n \in Marked :
    ConnectedToSomeButNotAll(n) \subseteq Marked \cup Frontier

(* ----------------------------------------------------------------------
   Invariant 2: every marked node is reachable via a bounded path
   ---------------------------------------------------------------------- *)
Inv2 ==
  \A n \in Marked : ReachableViaPath(n)

(* ----------------------------------------------------------------------
   Set of all nodes reachable from Root (within the bounded length)
   ---------------------------------------------------------------------- *)
ReachableSet ==
  { n \in Nodes : ReachableViaPath(n) }

(* ----------------------------------------------------------------------
   Invariant 3: when the algorithm is done, Marked equals the reachable set
   ---------------------------------------------------------------------- *)
Inv3 ==
  (pc = "Done") => (Marked = ReachableSet)

(* ----------------------------------------------------------------------
   Partial correctness: if the frontier is empty then Marked is the reachable set
   ---------------------------------------------------------------------- *)
PartialCorrectness ==
  (Frontier = {}) => (Marked = ReachableSet)

(* ----------------------------------------------------------------------
   Liveness property: eventual termination
   ---------------------------------------------------------------------- *)
Termination == <> (pc = "Done")

====