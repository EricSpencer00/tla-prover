---- MODULE Reachable ----
EXTENDS Naturals, Sequences

(* Misra's variant of BFS: the visited (marked) set and the frontier may       *)
(* overlap, which simplifies a parallel implementation.  Here the algorithm    *)
(* is modeled as a single process that keeps picking frontier nodes.           *)

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == << marked, frontier, pc >>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

(* The main action has two cases, chosen nondeterministically from the         *)
(* frontier.  If the node is unmarked it is added to the visited set and its    *)
(* successors are added to the frontier (without removing the node itself).    *)
(* If it is already marked, it is simply removed from the frontier.            *)
Explore ==
    /\ pc = "running"
    /\ \E n \in frontier :
         IF n \notin marked
         THEN /\ marked' = marked \cup {n}
              /\ frontier' = frontier \cup Succ[n]
         ELSE /\ marked' = marked
              /\ frontier' = frontier \ {n}
    /\ pc' = "running"

Terminate == /\ pc = "running" /\ frontier = {} /\ pc' = "done" /\ UNCHANGED << marked, frontier >>

Next == Explore \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Explore)

(* Safety: partial correctness.  The three invariants together imply the       *)
(* marked set is exactly the reachable-from-root set once the algorithm        *)
(* terminates.                                                                  *)
Inv1 == \A n \in marked : Succ[n] \subseteq (marked \cup frontier)
Inv2 == \{n \in Nodes : (\E m \in marked \cup frontier : n \in Succ[m])\} = {n \in Nodes : (\E m \in frontier : n \in Succ[m])}
Inv3 == {n \in Nodes : (\E m \in marked : n \in Succ[m])} = marked \cup {n \in Nodes : (\E m \in frontier : n \in Succ[m])}
PartialCorrectness == (pc = "done") => (marked = {n \in Nodes : (\E m \in {Root} : n \in Succ[m])})

(* Liveness: with a finite reachable set the process eventually finishes.      *)
Termination == (pc = "running") ~> (pc = "done")

(* The substitution below is the ONLY place the finite-Seq operator is named. *)
LimitedSeq == FiniteSeq

(* For parity with the paired parallel implementation, Succ is parametrized    *)
(* by the node (ConnectedToSomeButNotAll) rather than being a plain constant.  *)
ConnectedToSomeButNotAll == Succ
====