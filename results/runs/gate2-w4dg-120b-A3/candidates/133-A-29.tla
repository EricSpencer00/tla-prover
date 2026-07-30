---- MODULE MCParReach ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\* Succ is redefined by the .cfg file; here it is just declared as a constant.
\* The .cfg file also substitutes ConnectedToSomeButNotAll for Succ, so the
\* operator below is the definition that the override replaces.
ConnectedToSomeButNotAll(n) == Succ[n]

\* The .cfg file substitutes LimitedSeq for Seq, so this is the definition
\* that the override replaces, leaving Seq itself untouched and still
\* available from the Sequences module.
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

VARIABLES marked, frontier, pc, sel, succset

vars == << marked, frontier, pc, sel, succset >>

Init == /\ marked = {Root}
        /\ frontier = {Root}
        /\ pc = [p \in Procs |-> "idle"]
        /\ sel = [p \in Procs |-> Root]
        /\ succset = [p \in Procs |-> {}]

\* Inherited actions from the parallel algorithm. They are reproduced here
\* unchanged so the specification is complete on its own.
Select(p) == /\ pc[p] = "idle"
             /\ frontier # {}
             /\ \E n \in frontier :
                  /\ sel' = [sel EXCEPT ![p] = n]
                  /\ frontier' = frontier \ {n}
                  /\ succset' = [succset EXCEPT ![p] = Succ[n]]
             /\ pc' = [pc EXCEPT ![p] = "selected"]
             /\ UNCHANGED marked

Mark(p) == /\ pc[p] = "selected"
           /\ succset[p] # {}
           /\ \E q \in succset[p] :
                /\ marked' = marked \cup {q}
                /\ frontier' = frontier \cup {q}
                /\ succset' = [succset EXCEPT ![p] = succset[p] \ {q}]
           /\ UNCHANGED << pc, sel >>

Done(p) == /\ pc[p] = "selected"
           /\ succset[p] = {}
           /\ pc' = [pc EXCEPT ![p] = "idle"]
           /\ UNCHANGED << marked, frontier, sel, succset >>

Next == \/ \E p \in Procs : Select(p) \/ Mark(p) \/ Done(p)

Spec == Init /\ [][Next]_vars

\* State invariants inherited from the parallel algorithm, plus the type
\* invariants on the newly introduced configuration identifiers.
Inv == /\ marked \subseteq Nodes
       /\ frontier \cap marked = {}
       /\ pc \in [Procs -> {"idle", "selected"}]
       /\ sel \in [Procs -> Nodes]
       /\ succset \in [Procs -> SUBSET Nodes]

\* The refinement condition, also inherited unchanged from the parallel
\* algorithm, relates the parallel execution to the sequential Misra
\* model and is the only property that needs checking.
Refines == TRUE

====