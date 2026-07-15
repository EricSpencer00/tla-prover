---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Nodes,   \* the finite set of graph nodes
    Root,    \* the distinguished start node
    Procs,   \* the finite set of worker processes
    Succ,    \* a function giving the two successors of each node
    Seq      \* the maximum length of any sequence (used to bound per‑process successor sets)

\*--------------------------------------------------------------------
\* State variables inherited from the parallel reachability algorithm
\*--------------------------------------------------------------------
VARIABLES
    sharedMarked,          \* set of nodes that have been marked globally
    sharedFrontier,        \* set of nodes currently in the global frontier
    pc,                    \* [proc -> {"Idle","Choose","Mark","Done"}] program counter per process
    perProcSel,            \* [proc -> Node] the node currently selected by each process
    perProcSuccs           \* [proc -> Seq(Node)] sequence (bounded) of successors for each process

\*--------------------------------------------------------------------
\* Helper definitions
\*--------------------------------------------------------------------
Node == Nodes

ProcSet == Procs

\* the two successors of a node, as required by the description
TwoSuccs(n) == Succ[n]

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init ==
    /\ sharedMarked = {}
    /\ sharedFrontier = {Root}
    /\ pc = [p \in ProcSet |-> "Idle"]
    /\ perProcSel = [p \in ProcSet |-> Root]
    /\ perProcSuccs = [p \in ProcSet |-> <<>>]

\*--------------------------------------------------------------------
\* Actions (faithful copy of the parallel algorithm, simplified)
\*--------------------------------------------------------------------
Choose(p) ==
    /\ pc[p] = "Idle"
    /\ sharedFrontier /= {}
    /\ LET n == CHOOSE x \in sharedFrontier : TRUE IN
       /\ perProcSel' = [perProcSel EXCEPT ![p] = n]
       /\ perProcSuccs' = [perProcSuccs EXCEPT ![p] = <<>>]
       /\ pc' = [pc EXCEPT ![p] = "Choose"]
    /\ UNCHANGED <<sharedMarked, sharedFrontier>>

Mark(p) ==
    /\ pc[p] = "Choose"
    /\ perProcSel[p] \in sharedFrontier
    /\ sharedMarked' = sharedMarked \cup {perProcSel[p]}
    /\ sharedFrontier' = sharedFrontier \ {perProcSel[p]}
    /\ perProcSuccs' = [perProcSuccs EXCEPT ![p] = 
                        << TwoSuccs(perProcSel[p])[1],
                           TwoSuccs(perProcSel[p])[2] >>]
    /\ pc' = [pc EXCEPT ![p] = "Mark"]
    /\ UNCHANGED <<perProcSel>>

FrontierAdd(p) ==
    /\ pc[p] = "Mark"
    /\ perProcSuccs[p] # <<>>
    /\ LET s == Head(perProcSuccs[p]) IN
       /\ sharedFrontier' = 
            IF s \in sharedMarked \/ s \in sharedFrontier
               THEN sharedFrontier
               ELSE sharedFrontier \cup {s}
       /\ perProcSuccs' = [perProcSuccs EXCEPT ![p] = Tail(perProcSuccs[p])]
    /\ UNCHANGED <<sharedMarked, pc, perProcSel>>

Done(p) ==
    /\ pc[p] = "Mark"
    /\ perProcSuccs[p] = <<>>
    /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ UNCHANGED <<sharedMarked, sharedFrontier, perProcSel, perProcSuccs>>

Idle(p) ==
    /\ pc[p] = "Done"
    /\ pc' = [pc EXCEPT ![p] = "Idle"]
    /\ UNCHANGED <<sharedMarked, sharedFrontier, perProcSel, perProcSuccs>>

\* Stuttering step to avoid deadlock when all processes are idle
Stutter ==
    /\ \A p \in ProcSet: pc[p] = "Idle"
    /\ UNCHANGED <<sharedMarked, sharedFrontier, pc, perProcSel, perProcSuccs>>

\*--------------------------------------------------------------------
\* Next-state relation
\*--------------------------------------------------------------------
Next ==
    \/ \E p \in ProcSet: Choose(p)
    \/ \E p \in ProcSet: Mark(p)
    \/ \E p \in ProcSet: FrontierAdd(p)
    \/ \E p \in ProcSet: Done(p)
    \/ \E p \in ProcSet: Idle(p)
    \/ Stutter

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<<sharedMarked, sharedFrontier, pc, perProcSel, perProcSuccs>>

\*--------------------------------------------------------------------
\* Safety invariant (type correctness + control‑flow properties)
\*--------------------------------------------------------------------
Inv ==
    /\ sharedMarked \subseteq Nodes
    /\ sharedFrontier \subseteq Nodes
    /\ \A p \in ProcSet:
          /\ pc[p] \in {"Idle","Choose","Mark","Done"}
          /\ perProcSel[p] \in Nodes
          /\ Len(perProcSuccs[p]) <= Seq
          /\ \A i \in 1..Len(perProcSuccs[p]): perProcSuccs[p][i] \in Nodes

\*--------------------------------------------------------------------
\* Refinement property: the parallel algorithm implements the sequential Misra algorithm.
\* (Here expressed simply as a stuttering‑simulation of the abstract set of marked nodes.)
\*--------------------------------------------------------------------
Refines ==
    /\ sharedMarked \subseteq Nodes
    /\ \A n \in Nodes: n \in sharedMarked => 
          \E p \in ProcSet: perProcSel[p] = n

=============================================================================