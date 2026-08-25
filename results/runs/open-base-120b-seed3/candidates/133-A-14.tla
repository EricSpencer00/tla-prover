---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ, NULL

(* Concrete graph: 4 nodes, each with exactly 2 successors *)
Nodes == {1, 2, 3, 4}
Root  == 1
Procs == {1, 2}
Succ  == [ n \in Nodes |-> 
            CASE n = 1 -> {2, 3}
                 [] n = 2 -> {3, 4}
                 [] n = 3 -> {4, 1}
                 [] n = 4 -> {1, 2}
         ]

(* Operator that will substitute for Succ in other modules *)
ConnectedToSomeButNotAll(n) == Succ[n]

(* Limited sequence operator that replaces Seq from Sequences *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

VARIABLES Marked, Frontier, pc, sel, succSet

vars == <<Marked, Frontier, pc, sel, succSet>>

(* Initial state *)
Init ==
    /\ Marked = {}
    /\ Frontier = {Root}
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> NULL]
    /\ succSet = [p \in Procs |-> {}]

(* Worker picks a node from the frontier *)
Pick(p) ==
    /\ pc[p] = "idle"
    /\ \E n \in Frontier :
          /\ sel'   = [sel   EXCEPT ![p] = n]
          /\ pc'    = [pc    EXCEPT ![p] = "busy"]
          /\ Frontier' = Frontier \ {n}
          /\ UNCHANGED <<Marked, succSet>>

(* Worker explores the successors of its selected node *)
Explore(p) ==
    /\ pc[p] = "busy"
    /\ LET n == sel[p] IN
         /\ succSet' = [succSet EXCEPT ![p] = ConnectedToSomeButNotAll(n)]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<Marked, Frontier, sel>>

(* Worker marks its discovered successors *)
Mark(p) ==
    /\ pc[p] = "done"
    /\ LET new == succSet[p] \ Marked IN
         /\ Marked'   = Marked \cup new
         /\ Frontier' = Frontier \cup new
    /\ pc'    = [pc    EXCEPT ![p] = "idle"]
    /\ sel'   = [sel   EXCEPT ![p] = NULL]
    /\ succSet' = [succSet EXCEPT ![p] = {}]
    /\ UNCHANGED <<>>

(* Overall next-state relation *)
Next ==
    \/ \E p \in Procs : Pick(p)
    \/ \E p \in Procs : Explore(p)
    \/ \E p \in Procs : Mark(p)

(* Specification formula *)
Spec == Init /\ [][Next]_vars

(* Inductive invariant *)
Inv ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ pc \in [Procs -> {"idle", "busy", "done"}]
    /\ sel \in [Procs -> (Nodes \cup {NULL})]
    /\ succSet \in [Procs -> SUBSET Nodes]

(* Refinement property (trivially true placeholder) *)
Refines == TRUE

====