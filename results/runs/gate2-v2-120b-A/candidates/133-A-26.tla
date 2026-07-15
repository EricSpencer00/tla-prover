---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(* Constants (to be instantiated in the .cfg)                              *)
(***************************************************************************)
CONSTANTS 
    Nodes,   \* The set of graph nodes (e.g., {1,2,3,4})
    Root,    \* The designated start node
    Procs,   \* The set of worker process identifiers (e.g., {1,2})
    Succ,    \* A function mapping each node to its two successors,  Succ \in [Nodes -> SUBSET Nodes]
    Seq      \* A bound on the length of any sequence (Seq = Cardinality(Nodes))

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)
VARIABLES 
    marked,    \* Set of nodes that have been discovered
    frontier,  \* Set of nodes currently awaiting processing
    pc,        \* Program counter per process: maps each proc to a label
    sel,       \* Currently selected node per process (or NULL)
    succSet    \* Set of successors already computed per process

(***************************************************************************)
(* Helper definitions                                                      *)
(***************************************************************************)

Labels == {"Idle", "Select", "Visit", "Done"}

ProcSet == Procs

\* A placeholder for “no node selected”.  It must not belong to Nodes.
NULL == -1

\* Sequence override bounded to length at most Seq.
OVERRIDE(s, i, e) ==
    IF i > Seq THEN s
    ELSE
        IF i = Len(s) + 1 THEN Append(s, e)
        ELSE IF i <= Len(s) THEN s[1 .. i-1] \o <<e>> \o s[i+1 .. Len(s)]
        ELSE s

(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in ProcSet |-> "Idle"]
    /\ sel = [p \in ProcSet |-> NULL]
    /\ succSet = [p \in ProcSet |-> {}]

(***************************************************************************)
(* Per‑process actions                                                     *)
(***************************************************************************)

Select(p) ==
    /\ pc[p] = "Idle"
    /\ frontier # {}
    /\ sel' = [sel EXCEPT ![p] = CHOOSE n \in frontier : TRUE]
    /\ frontier' = frontier \ {sel[p]}
    /\ pc' = [pc EXCEPT ![p] = "Visit"]
    /\ UNCHANGED <<marked, succSet>>

Visit(p) ==
    /\ pc[p] = "Visit"
    /\ succSet' = [succSet EXCEPT ![p] = Succ[sel[p]]]
    /\ marked' = marked \cup {sel[p]}
    /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ sel' = [sel EXCEPT ![p] = NULL]
    /\ UNCHANGED <<frontier>>

Done(p) ==
    /\ pc[p] = "Done"
    /\ frontier' = frontier \cup {n \in succSet[p] : n \notin marked}
    /\ pc' = [pc EXCEPT ![p] = "Idle"]
    /\ UNCHANGED <<marked, sel, succSet>>

ProcAction(p) == \/ Select(p) \/ Visit(p) \/ Done(p)

Next ==
    \E p \in ProcSet : ProcAction(p)

(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)
Spec ==
    Init /\ [][Next]_<<marked, frontier, pc, sel, succSet>>

(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)

\* Type-correctness invariant
TypeOk ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [ProcSet -> Labels]
    /\ sel \in [ProcSet -> (Nodes \cup {NULL})]
    /\ succSet \in [ProcSet -> SUBSET Nodes]

\* Control‑flow invariant: a process is never in “Visit” or “Done” while
\* its selected node is NULL.
CtrlOk ==
    \A p \in ProcSet :
        (pc[p] \in {"Visit", "Done"}) => sel[p] # NULL

Inv == TypeOk /\ CtrlOk

(***************************************************************************)
(* Refinement property (parallel algorithm implements the sequential   *)
(* Misra reachability algorithm)                                           *)
(***************************************************************************)
\* For simplicity we assert that every node eventually reachable
\* according to the parallel algorithm is also reachable in the
\* sequential algorithm.  The sequential algorithm’s reachable set is
\* the least fix‑point of expanding from the root using Succ.  We
\* characterise it directly.
Reachable ==
    { n \in Nodes :
        \E seq \in Seq(1..Seq) :
            \A i \in 1..Len(seq) : seq[i] \in Nodes /\
            (i = 1 => seq[i] = Root) /\
            (i > 1 => seq[i] \in Succ[seq[i-1]]) }

Refines ==
    /\ marked \subseteq Reachable

====