---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME /\ 0 < N
       /\ 2 * T < N
       /\ F \in 0..T
       /\ Bottom \notin Values

\* Control locations, following the two-phase protocol plus crash and a
\* deterministic-choose fallback.
CONSTANTS Phase1Broad, Phase1Wait, Phase2Broad, Phase2Wait, Done, Crashed, Choosing
Locations == {Phase1Broad, Phase1Wait, Phase2Broad, Phase2Wait, Done, Crashed, Choosing}

MsgTypes == {"phase1", "phase2"}

VARIABLES loc, view, proposal, estimate, decision, crashedCount, sent, received

vars == <<loc, view, proposal, estimate, decision, crashedCount, sent, received>>

Bump(x) == IF x < Cardinality(Values) THEN x + 1 ELSE x

Msgs == [type: MsgTypes, value: Values \cup {Bottom}, sender: 1..N, estimate: Values \cup {Bottom}]

Quorum == N - T

MaxVal(vs) == CHOOSE x \in vs : \A y \in vs : y <= x

TypeOK ==
  /\ loc \in [1..N -> Locations]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ proposal \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashedCount \in 0..F
  /\ sent \subseteq Msgs
  /\ received \in [1..N -> SUBSET Msgs]

Init ==
  /\ loc = [p \in 1..N |-> Phase1Broad]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ proposal \in [1..N -> Values]
  /\ estimate = [p \in 1..N |-> Bottom]
  /\ decision = [p \in 1..N |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ received = [p \in 1..N |-> {}]

BumpProposal(p) ==
  LET val == proposal[p] IN LET idx == CHOOSE i \in 1..Cardinality(Values) :
                             CHOOSE x \in Values : Bump(i) = x /\ x = val
                       IN Values[(idx % Cardinality(Values)) + 1]

BroadcastPhase1(p) ==
  /\ loc[p] = Phase1Broad
  /\ sent' = sent \cup {[type |-> "phase1", value |-> proposal[p], sender |-> p,
                         estimate |-> Bottom]}
  /\ loc' = [loc EXCEPT ![p] = Phase1Wait]
  /\ proposal' = [proposal EXCEPT ![p] = BumpProposal(p)]
  /\ UNCHANGED <<view, estimate, decision, crashedCount, received>>

Receive(p, m) ==
  /\ loc[p] \in {Phase1Wait, Phase2Wait}
  /\ m.type = IF loc[p] = Phase1Wait THEN "phase1" ELSE "phase2"
  /\ view' = [view EXCEPT ![p][m.sender] = m.value]
  /\ received' = [received EXCEPT ![p] = @ \cup {m}]
  /\ UNCHANGED <<loc, proposal, estimate, decision, crashedCount, sent>>

MoveToPhase2(p) ==
  /\ loc[p] = Phase1Wait
  /\ Cardinality({m \in received[p] : m.type = "phase1"}) >= Quorum
  /\ estimate' = [estimate EXCEPT ![p] = MaxVal({view[p][q] : q \in 1..N})]
  /\ loc' = [loc EXCEPT ![p] = Phase2Broad]
  /\ UNCHANGED <<view, proposal, decision, crashedCount, sent, received>>

BroadcastPhase2(p) ==
  /\ loc[p] = Phase2Broad
  /\ sent' = sent \cup {[type |-> "phase2", value |-> proposal[p], sender |-> p,
                         estimate |-> estimate[p]]}
  /\ loc' = [loc EXCEPT ![p] = Phase2Wait]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashedCount, received>>

DecideQuorum(p) ==
  /\ loc[p] = Phase2Wait
  /\ \E ev \in Values :
       /\ Cardinality({m \in received[p] : m.type = "phase2" /\ m.estimate = ev})
          >= Quorum
       /\ decision' = [decision EXCEPT ![p] = ev]
  /\ loc' = [loc EXCEPT ![p] = Done]
  /\ UNCHANGED <<view, proposal, estimate, crashedCount, sent, received>>

Choose(p) ==
  /\ loc[p] = Phase2Wait
  /\ Cardinality({m \in received[p] : m.type = "phase2"}) = N
  /\ \E ev \in Values :
       /\ ev \in {view[p][q] : q \in 1..N}
       /\ decision' = [decision EXCEPT ![p] = ev]
  /\ loc' = [loc EXCEPT ![p] = Choosing]
  /\ UNCHANGED <<view, proposal, estimate, crashedCount, sent, received>>

Crash(p) ==
  /\ crashedCount < F
  /\ loc[p] \notin {Crashed, Done}
  /\ loc' = [loc EXCEPT ![p] = Crashed]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED <<view, proposal, estimate, decision, sent, received>>

Next ==
  \/ \E p \in 1..N : BroadcastPhase1(p)
  \/ \E p \in 1..N, m \in sent : Receive(p, m)
  \/ \E p \in 1..N : MoveToPhase2(p)
  \/ \E p \in 1..N : BroadcastPhase2(p)
  \/ \E p \in 1..N : DecideQuorum(p)
  \/ \E p \in 1..N : Choose(p)
  \/ \E p \in 1..N : Crash(p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in 1..N, m \in sent : Receive(p, m))
        /\ WF_vars(\E p \in 1..N : MoveToPhase2(p))
        /\ WF_vars(\E p \in 1..N : DecideQuorum(p))
        /\ WF_vars(\E p \in 1..N : Choose(p))
        /\ SF_vars(\E p \in 1..N : BroadcastPhase1(p))
        /\ SF_vars(\E p \in 1..N : BroadcastPhase2(p))

Validity == \A p \in 1..N : decision[p] # Bottom => decision[p] \in Values

Agreement == \A p, q \in 1..N : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Termination == <>(\A p \in 1..N : loc[p] \in {Done, Crashed})

ConditionC1 == (\A p \in 1..N : proposal[p] \in Values)
              /\ Cardinality({p \in 1..N : proposal[p] = MaxVal(Values)}) >= F + 1
              => Termination

Properties == Termination /\ ConditionC1

====