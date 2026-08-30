---- MODULE ReachableProofs ----
EXTENDS ReachabilityAlgorithm, ReachabilityProofs

CONSTANTS Nodes, Root

\* Inherited state: Marked, Frontier, pc. We add the combined-invariant
\* variable and a junction to route the two-step completion into DONE.
VARIABLES Marked, Frontier, pc, CombinedInvHolds

vars == <<Marked, Frontier, pc, CombinedInvHolds>>

TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"init", "running", "done"}
  /\ CombinedInvHolds \in BOOLEAN

Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "init"
  /\ CombinedInvHolds = FALSE

Start ==
  /\ pc = "init"
  /\ pc' = "running"
  /\ UNCHANGED <<Marked, Frontier, CombinedInvHolds>>

Expand(n) ==
  /\ pc = "running"
  /\ n \in Frontier
  /\ Marked' = Marked \cup {n}
  /\ Frontier' = (Frontier \ {n}) \cup {m \in Nodes : (n, m) \in Edges}
  /\ UNCHANGED <<pc, CombinedInvHolds>>

Stall ==
  /\ pc = "running"
  /\ Frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<Marked, Frontier, CombinedInvHolds>>

ComputeCombinedInv ==
  /\ pc = "done"
  /\ CombinedInvHolds' = ReachableFrom(Frontier) \cup Marked = ReachableFrom(Nodes)
  /\ UNCHANGED <<Marked, Frontier, pc>>

Next ==
  \/ Start
  \/ \E n \in Nodes : Expand(n)
  \/ Stall
  \/ ComputeCombinedInv

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Start)
  /\ \A n \in Nodes : SF_vars(Expand(n))

\* The three invariants are proved separately from the model checking; they
\* are not derived here, only stated for TLAPS to consume. The final theorem
\* is the partial-correctness statement linking termination to exactness.
Invariant1 ==
  /\ TypeOK
  /\ \A n \in Marked : Succ(n) \subseteq Marked \cup Frontier

Invariant2 ==
  \* Reachability Lemma 1: ReachableFrom(Marked \cup Frontier) = Marked \cup ReachableFrom(Frontier)
  ReachableFrom(ReachableFrom(Frontier) \cup Marked) = Marked \cup ReachableFrom(Frontier)

Invariant3 ==
  /\ \A S \in SUBSET Nodes : ReachableFrom(ReachableFrom(S)) = ReachableFrom(S)
  /\ ReachableFrom({Root}) = Marked \cup ReachableFrom(Frontier)

INVARIANTS == {Invariant1, Invariant2, Invariant3}

PartialCorrectness ==
  (pc = "done") => (Marked = ReachableFrom({Root}))

PROPERTIES == {PartialCorrectness}
====