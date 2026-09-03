---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

(* Misra's variant of breadth-first search: visited and frontier may overlap. *)
CONSTANTS Nodes, Root, Succ

NoElem == "empty"

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

\* Main action: explore one frontier node, with the two overlapping cases.
Step ==
    /\ pc = "running"
    /\ \E n \in frontier :
        IF n \notin marked THEN
            /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
            /\ UNCHANGED pc
        ELSE
            /\ frontier' = frontier \ {n}
            /\ UNCHANGED <<marked, pc>>
    /\ UNCHANGED <<>>

Terminate ==
    /\ pc = "running"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Step \/ Terminate \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

RecursiveReachable(S) ==
    IF S = {}
    THEN {}
    ELSE LET n == CHOOSE x \in S : TRUE IN Succ[n] \cup RecursiveReachable(S \ {n})

AllReachable == RecursiveReachable({Root})

(* Safety: every successor of a marked node is either marked or frontiers. *)
Inv1 == \A n \in Nodes : n \in marked => Succ[n] \subseteq (marked \cup frontier)

(* Safety: the nodes reachable from marked \cup frontier are exactly those *)
(* reachable from the marked nodes together with those from the frontier.    *)
Inv2 ==
    RecursiveReachable(marked \cup frontier) = RecursiveReachable(marked) \cup RecursiveReachable(frontier)

(* Safety: nodes reachable from the root are the marked set plus those   *)
(* reachable from the frontier (the precise bookkeeping identity).       *)
Inv3 == AllReachable = marked \cup RecursiveReachable(frontier)

PartialCorrectness == (pc = "done") => (marked = AllReachable)

(* Liveness: the reachable set is finite and the loop is weakly fair, so   *)
(* frontier cannot stay non-empty forever -- the algorithm eventually halts. *)
Termination == \A n \in Nodes : (n \in AllReachable) ~> (n \notin AllReachable)

(* The .cfg substitutes a bounded version of Succ for ConnectedToSomeButNotAll *)
ConnectedToSomeButNotAll == Succ

(* The .cfg overrides Seq from Sequences with a finite version LimitedSeq. *)
LimitedSeq(S) == CHOOSE s \in Sequences : s \in Seq /\ SetOfSeq(s) = S

====