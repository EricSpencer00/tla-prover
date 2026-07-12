---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

(* Type correctness invariant: both sets contain only graph nodes *)
TypeOK == /\ marked \subseteq Nodes
         /\ frontier \subseteq Nodes
         /\ pc \in {"Running", "Terminated"}

(* Initial condition *)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Running"

(* Main action: nondeterministically pick a node from the frontier *)
Main ==
    /\ pc = "Running"
    /\ frontier # {}
    /\ \E node \in frontier :
          IF node \notin marked THEN
              /\ marked' = marked \cup {node}
              /\ frontier' = frontier \cup Succ(node)
              /\ pc' = pc
          ELSE
              /\ marked' = marked
              /\ frontier' = frontier \ {node}
              /\ pc' = pc

(* Termination: when the frontier is empty, move to the terminated state *)
Terminate ==
    /\ pc = "Running"
    /\ frontier = {}
    /\ pc' = "Terminated"
    /\ UNCHANGED marked

(* The next-state relation *)
NEXT == Main \/ Terminate

(* Full specification *)
Spec == Init /\ [][NEXT]_<<marked, frontier, pc>>

(* Safety invariant 1: every successor of a marked node is either marked or in the frontier *)
Inv1 == \A node \in marked : Succ(node) \subseteq marked \cup frontier

(* Safety invariant 2: the union of marked and frontier is closed under the successor relation *)
Inv2 == \A node \in marked \cup frontier :
            Succ(node) \subseteq marked \cup frontier

(* Safety invariant 3: nodes reachable from the root are exactly those in marked plus those reachable from frontier *)
Inv3 ==
    (Nodes \ {Root}) \subseteq (marked \cup frontier) /\
    (\A node \in (marked \cup frontier) :
        \A succ \in Succ(node) : succ \in (marked \cup frontier))

(* Partial correctness invariant: when the algorithm terminates, the marked set equals the set of nodes reachable from Root *)
PartialCorrectness ==
    (pc = "Terminated") => (marked = {Root} \cup (Succ* (marked)))

(* The set of nodes reachable from a set S using the transitive closure of Succ *)
SuccStar(S) == S \cup {s \in SuccSet : \E node \in S : s \in Succ(node)}  (* iterative closure *)

(* Helper: the transitive closure of Succ over the entire graph *)
SuccTransitive ==
    \E nodes \in Subset(Nodes) :
        (\A node \in nodes : Succ(node) \subseteq nodes)

(* Helper: the set of nodes reachable from Root using the transitive closure of Succ *)
RootReachable ==
    {n \in Nodes : \E path \in Seq : path[1] = Root /\ \A i \in 1..Len(path)-1 :
                 path[i+1] \in Succ(path[i])}

(* Liveness property: if the reachable set is finite, the algorithm eventually reaches the terminated state *)
Termination == TERMINATED

====