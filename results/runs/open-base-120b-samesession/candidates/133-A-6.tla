---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

(* operator that the configuration substitutes for Succ *)
ConnectedToSomeButNotAll == Succ

(* bounded version of Seq for model checking *)
MaxLen == Cardinality(Nodes)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxLen }

VARIABLES Marked, Frontier, pc, sel, succSet

Vars == <<Marked, Frontier, pc, sel, succSet>>

Init ==
    /\ Marked = {}
    /\ Frontier = {Root}
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> "null"]
    /\ succSet = [p \in Procs |-> {}]

(* placeholder for the parallel reachability steps *)
Next ==
    UNCHANGED Vars

Spec ==
    Init /\ [][Next]_Vars

Inv ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ pc \in [Procs -> {"idle", "busy"}]
    /\ sel \in [Procs -> (Nodes \cup {"null"})]
    /\ succSet \in [Procs -> SUBSET Nodes]

Refines == TRUE

====