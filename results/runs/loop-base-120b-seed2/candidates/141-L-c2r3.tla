---- MODULE Reachable ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

(* Relation derived from the successor function, for use with TC *)
SuccRel == { << n , m >> : n \in Nodes /\ m \in Succ[n] }

(* Reachable nodes from a set S (reflexive transitive closure) *)
Reach(S) == S \cup (TC(SuccRel))[S]

(* Operator substituted for Succ in the .cfg file *)
ConnectedToSomeButNotAll(n) == Succ[n]

(* Finite version of Seq, used by the .cfg replacement *)
LimitedSeq(S) == Seq(S)

vars == << marked , frontier , pc >>

Init ==
    /\ marked = {}
    /\ frontier = { Root }
    /\ pc = "Run"

Action ==
    \/ \E n \in frontier :
          /\ n \notin marked
          /\ marked'   = marked \cup { n }
          /\ frontier' = frontier \cup Succ[n]
          /\ pc'       = pc
    \/ \E n \in frontier :
          /\ n \in marked
          /\ frontier' = frontier \ { n }
          /\ marked'   = marked
          /\ pc'       = pc
    \/ /\ frontier = {}
       /\ pc = "Run"
       /\ pc' = "Done"
       /\ UNCHANGED << marked , frontier >>

Spec == Init /\ [][Action]_vars /\ WF_vars(Action)

TypeOK ==
    /\ marked   \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in { "Run", "Done" }

Inv1 == \A m \in marked : Succ[m] \subseteq marked \cup frontier

Inv2 == marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 == Reach({ Root }) = marked \cup Reach(frontier)

PartialCorrectness == (frontier = {}) => (marked = Reach({ Root }))

Termination == <> (frontier = {})

====