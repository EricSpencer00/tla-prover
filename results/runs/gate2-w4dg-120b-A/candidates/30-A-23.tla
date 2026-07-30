---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME Bottom \notin Values

Locs == {"broadcast_phase1", "waiting_phase1", "prepare", "broadcast_phase2",
          "waiting_phase2", "done", "crashed", "choosing"}

Msgs == [type: {"phase1", "phase2"}, val: Values, est: Values \cup {Bottom},
         sender: 1..N]

Majority == N - T

VARIABLES loc, view, propose, estimate, decided, crashCount, sent, got

vars == <<loc, view, propose, estimate, decided, crashCount, sent, got>>

MaxVal(S) == CHOOSE m \in S : \A x \in S : x <= m

TypeOK ==
    /\ loc \in [1..N -> Locs]
    /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
    /\ propose \in [1..N -> Values]
    /\ estimate \in [1..N -> Values \cup {Bottom}]
    /\ decided \in [1..N -> Values \cup {Bottom}]
    /\ crashCount \in 0..F
    /\ sent \subseteq Msgs
    /\ got \in [1..N -> SUBSET Msgs]

Init ==
    /\ loc = [p \in 1..N |-> "broadcast_phase1"]
    /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
    /\ propose \in [1..N -> Values]
    /\ estimate = [p \in 1..N |-> Bottom]
    /\ decided = [p \in 1..N |-> Bottom]
    /\ crashCount = 0
    /\ sent = {}
    /\ got = [p \in 1..N |-> {}]

\* No message ever carries a value larger than what has actually been
\* proposed, so the maximum possible estimate is bounded by that max.
PossibleEstimates == {propose[p] : p \in 1..N}

\* Phase 1: each process broadcasts its proposal.
BroadcastPhase1(p) ==
    /\ loc[p] = "broadcast_phase1"
    /\ sent' = sent \cup {[type |-> "phase1", val |-> propose[p],
                           est |-> Bottom, sender |-> p]}
    /\ loc' = [loc EXCEPT ![p] = "waiting_phase1"]
    /\ UNCHANGED <<view, propose, estimate, decided, crashCount, got>>

\* Receiving a phase-1 message updates the local view.
ReceivePhase1(p, m) ==
    /\ loc[p] \in {"waiting_phase1", "waiting_phase2"}
    /\ m \in got[p]
    /\ m.type = "phase1"
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ got' = [got EXCEPT ![p] = got[p] \ {m}]
    /\ UNCHANGED <<loc, propose, estimate, decided, crashCount, sent>>

\* After a phase-1 majority the process estimates the maximum it has seen.
Prepare(p) ==
    /\ loc[p] = "waiting_phase1"
    /\ Cardinality({m \in got[p] : m.type = "phase1"}) >= Majority
    /\ estimate' = [estimate EXCEPT ![p] = MaxVal({view[p][q] : q \in 1..N})]
    /\ loc' = [loc EXCEPT ![p] = "broadcast_phase2"]
    /\ UNCHANGED <<view, propose, decided, crashCount, sent, got>>

\* Phase 2: each process broadcasts its proposal and its estimate.
BroadcastPhase2(p) ==
    /\ loc[p] = "broadcast_phase2"
    /\ sent' = sent \cup {[type |-> "phase2", val |-> propose[p],
                           est |-> estimate[p], sender |-> p]}
    /\ loc' = [loc EXCEPT ![p] = "waiting_phase2"]
    /\ UNCHANGED <<view, propose, estimate, decided, crashCount, got>>

\* A phase-2 majority on the same estimate lets the process decide it.
Decide(p) ==
    /\ loc[p] = "waiting_phase2"
    /\ \E m \in Values :
         /\ Cardinality({mm \in got[p] : mm.type = "phase2" /\ mm.est = m})
              >= Majority
         /\ decided' = [decided EXCEPT ![p] = m]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, propose, estimate, crashCount, sent, got>>

\* A process that cannot reach a majority chooses any value it has seen.
Choose(p) ==
    /\ loc[p] = "waiting_phase2"
    /\ \A m \in Values :
         Cardinality({mm \in got[p] : mm.type = "phase2" /\ mm.est = m})
             < Majority
    /\ loc' = [loc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<view, propose, estimate, decided, crashCount, sent, got>>

\* Deterministic choice: the process picks the smallest value it has seen.
Select(p) ==
    /\ loc[p] = "choosing"
    /\ decided' = [decided EXCEPT ![p] =
                     CHOOSE v \in {view[p][q] : q \in 1..N} : \A w \in
                         {view[p][q] : q \in 1..N} : v <= w]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, propose, estimate, crashCount, sent, got>>

\* A process may crash, provided the bound on crashed processes is not reached.
Crash(p) ==
    /\ loc[p] \notin {"crashed", "done"}
    /\ crashCount < F
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ crashCount' = crashCount + 1
    /\ UNCHANGED <<view, propose, estimate, decided, sent, got>>

Next ==
    \/ \E p \in 1..N : BroadcastPhase1(p)
    \/ \E p \in 1..N, m \in Msgs : ReceivePhase1(p, m)
    \/ \E p \in 1..N : Prepare(p)
    \/ \E p \in 1..N : BroadcastPhase2(p)
    \/ \E p \in 1..N : Decide(p)
    \/ \E p \in 1..N : Choose(p)
    \/ \E p \in 1..N : Select(p)
    \/ \E p \in 1..N : Crash(p)

Spec == Init /\ [][Next]_vars
        /\ \A p \in 1..N : WF_vars(ReceivePhase1(p, CHOOSE m \in got[p] : TRUE))
        /\ \A p \in 1..N : WF_vars(Prepare(p))
        /\ \A p \in 1..N : WF_vars(BroadcastPhase2(p))
        /\ \A p \in 1..N : WF_vars(Decide(p))
        /\ \A p \in 1..N : WF_vars(Select(p))
        /\ \A p \in 1..N : WF_vars(Choose(p))

\* Every decision is a value that at least one process actually proposed.
Validity == \A p \in 1..N : decided[p] # Bottom => decided[p] \in {propose[q] : q \in 1..N}

Agreement == \A p, q \in 1..N :
                 (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

Termination == <>(\A p \in 1..N : loc[p] \in {"crashed", "done"})

C1 == (\E p \in 1..N : propose[p] = MaxVal(Values))
ConditionCTermination == C1 ~> Termination

Properties == Termination /\ ConditionCTermination

====