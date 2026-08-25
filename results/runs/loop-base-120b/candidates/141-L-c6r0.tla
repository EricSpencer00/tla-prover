---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

(* Operator substituted for Succ in the configuration *)
ConnectedToSomeButNotAll(n) == Succ[n]

(* Finite version of Seq, used when the configuration replaces Seq with LimitedSeq *)
LimitedSeq(S) ==
    { <<>> } \cup
    { <<x>> : x \in S } \cup
    { <<x, y>> : x \in S /\ y \in S }

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

(* Initial state *)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"

(* Reachability definitions *)
RECURSIVE ReachStar(_)
ReachStar(n) ==
    {n} \cup UNION { ReachStar(m) : m \in Succ[n] }

Reach(S) == UNION { ReachStar(n) : n \in S }

(* Main algorithmic actions *)
MainAction ==
    \/ \E n \in frontier :
          /\ n \notin marked
          /\ marked'   = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
          /\ pc'       = pc
    \/ \E n \in frontier :
          /\ n \in marked
          /\ marked'   = marked
          /\ frontier' = frontier \ {n}
          /\ pc'       = pc

(* Termination action when the frontier is empty *)
TerminateAction ==
    /\ frontier = {}
    /\ pc'       = "Done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ MainAction
    \/ TerminateAction

(* Specification *)
Spec ==
    Init /\ [][Next]_vars

(* Invariants *)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Run", "Done"}

Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
    marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 ==
    Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
    pc = "Done" => marked = Reach({Root})

(* Liveness property *)
Termination ==
    <> (pc = "Done")

====