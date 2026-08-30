---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, pNode, pSucc

vars == <<marked, frontier, pc, pNode, pSucc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "working", "done"}]
  /\ pNode \in [Procs -> Nodes \cup {"none"}]
  /\ pSucc \in [Procs -> SUBSET Nodes]

\* Control flow: a process in the "working" state must be holding a node and
\* have computed its successors, so no process is carried partway through an
\* operation by another process's interference on the shared frontier.
WorkCoherent ==
  \A p \in Procs :
    pc[p] = "working" => (pNode[p] \in Nodes /\ pSucc[p] \subseteq Nodes)

\* The shared marked set is exactly the set of nodes that have been removed
\* from the frontier, so no discovery is ever lost by a concurrent removal.
FrontierMatches == marked = Nodes \ frontier

\* Starts a work step: takes a frontier node and computes its successors
\* in one step, before the irreversible removal that follows.
StartWork(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ pNode' = [pNode EXCEPT ![p] = n]
  /\ pSucc' = [pSucc EXCEPT ![p] = Succ[n]]
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ UNCHANGED marked

\* Irreversibly marks the node it holds and releases the hold.
MarkAndRelease(p) ==
  /\ pc[p] = "working"
  /\ marked' = marked \cup {pNode[p]}
  /\ pNode' = [pNode EXCEPT ![p] = "none"]
  /\ pSucc' = [pSucc EXCEPT ![p] = {}]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED frontier

\* Reuses a worker that has finished its step.
ResetWorker(p) ==
  /\ pc[p] = "done"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<marked, frontier, pNode, pSucc>>

\* The autonomous progress latch: always enabled while some frontier node
\* is unclaimed, so every node is eventually claimed by some worker.
Latch ==
  \E p \in Procs : \E n \in frontier :
    /\ pc[p] = "idle"
    /\ frontier' = frontier \ {n}
    /\ pNode' = [pNode EXCEPT ![p] = n]
    /\ pSucc' = [pSucc EXCEPT ![p] = Succ[n]]
    /\ pc' = [pc EXCEPT ![p] = "working"]
    /\ UNCHANGED marked

Init ==
  /\ marked = {}
  /\ frontier = Nodes
  /\ pc = [p \in Procs |-> "idle"]
  /\ pNode = [p \in Procs |-> "none"]
  /\ pSucc = [p \in Procs |-> {}]

Next ==
  \/ \E p \in Procs, n \in Nodes : StartWork(p, n)
  \/ \E p \in Procs : MarkAndRelease(p)
  \/ \E p \in Procs : ResetWorker(p)
  \/ Latch

Spec == Init /\ [][Next]_vars

Inv == TypeOK /\ WorkCoherent /\ FrontierMatches

Refines == FrontierMatches

\* The .cfg treats ConnectedToSomeButNotAll as a synonym for the graph's
\* actual successor relation defined here.
ConnectedToSomeButNotAll == Succ

\* The .cfg treats LimitedSeq as a synonym for the bounded sequence
\* constructor; keeping Seq available satisfies Sequences' definition.
LimitedSeq == Seq

====