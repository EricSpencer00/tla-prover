---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES loc, view, proposed, estimate, decision, crashed, sent, received
vars == <<loc, view, proposed, estimate, decision, crashed, sent, received>>

Phase1 == "p1"
Phase2 == "p2"
MsgTypes == {Phase1, Phase2}

RECURSIVE MaxV(_)
MaxV(S) ==
  IF S = {} THEN Bottom
  ELSE LET x == CHOOSE y \in S : \A z \in S : y >= z IN x

\* Max over the row of the local view matrix for one process.
MaxVal(p) == MaxV({view[p][i] : i \in 1..N})

TypeOK ==
  /\ loc \in [1..N -> {"b1", "w1", "p1", "b2", "w2", "done", "crashed", "choose"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ proposed \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq [type: MsgTypes, val: Values, from: 1..N, est: Values \cup {Bottom}]
  /\ received \in [1..N -> SUBSET [type: MsgTypes, val: Values, from: 1..N, est: Values \cup {Bottom}]]

Init ==
  /\ loc = [p \in 1..N |-> "b1"]
  /\ view = [p \in 1..N |-> [i \in 1..N |-> Bottom]]
  /\ proposed \in [1..N -> Values]
  /\ estimate = [p \in 1..N |-> Bottom]
  /\ decision = [p \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ received = [p \in 1..N |-> {}]

BroadcastPhase1(p) ==
  /\ loc[p] = "b1"
  /\ sent' = sent \cup {[type |-> Phase1, val |-> proposed[p], from |-> p, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![p] = "w1"]
  /\ UNCHANGED <<view, proposed, estimate, decision, crashed, received>>

\* Messages are buffered and delivered in any order.
ReceivePhase1(p, m) ==
  /\ loc[p] \in {"w1", "p1"}
  /\ m \in sent
  /\ m.type = Phase1
  /\ view[p][m.from] = Bottom
  /\ view' = [view EXCEPT ![p][m.from] = m.val]
  /\ UNCHANGED <<loc, sent, proposed, estimate, decision, crashed, received>>

Phase1ToPhase2(p) ==
  /\ loc[p] = "w1"
  /\ Cardinality({m \in received[p] : m.type = Phase1}) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = MaxVal(p)]
  /\ sent' = sent \cup {[type |-> Phase2, val |-> proposed[p], from |-> p, est |-> MaxVal(p)]}
  /\ loc' = [loc EXCEPT ![p] = "p1"]
  /\ UNCHANGED <<view, proposed, decision, crashed, received>>

ReceivePhase2(p, m) ==
  /\ loc[p] \in {"p1", "w2"}
  /\ m \in sent
  /\ m.type = Phase2
  /\ received' = [received EXCEPT ![p] = @ \cup {m}]
  /\ UNCHANGED <<loc, view, proposed, estimate, decision, crashed, sent>>

\* The N-T threshold here is Condition C1 from the paper.
DecideOnEstimate(p, v) ==
  /\ loc[p] = "p1"
  /\ Cardinality({m \in received[p] : m.type = Phase2 /\ m.est = v}) >= N - T
  /\ decision' = [decision EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, proposed, estimate, crashed, sent, received>>

\* Deterministically picking the current maximum is lossless and keeps the model finite.
MoveToChoosing(p) ==
  /\ loc[p] = "p1"
  /\ ~(\E v \in Values : Cardinality({m \in received[p] : m.type = Phase2 /\ m.est = v}) >= N - T)
  /\ Cardinality({m \in received[p] : m.type = Phase2}) = N
  /\ loc' = [loc EXCEPT ![p] = "choose"]
  /\ UNCHANGED <<view, proposed, estimate, decision, crashed, sent, received>>

ChooseAndDecide(p, v) ==
  /\ loc[p] = "choose"
  /\ v \in {view[p][i] : i \in 1..N /\ view[p][i] # Bottom}
  /\ decision' = [decision EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, proposed, estimate, crashed, sent, received>>

Crash(p) ==
  /\ crashed < F
  /\ crashed' = crashed + 1
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ UNCHANGED <<view, proposed, estimate, decision, sent, received>>

Next ==
  \/ \E p \in 1..N : BroadcastPhase1(p) \/ Phase1ToPhase2(p) \/ MoveToChoosing(p) \/ Crash(p)
  \/ \E p \in 1..N, v \in Values : DecideOnEstimate(p, v) \/ ChooseAndDecide(p, v)
  \/ \E p \in 1..N, m \in sent : ReceivePhase1(p, m) \/ ReceivePhase2(p, m)

Spec ==
  /\ TypeOK
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..N : BroadcastPhase1(p))
  /\ WF_vars(\E p \in 1..N : \E m \in sent : ReceivePhase1(p, m))
  /\ WF_vars(\E p \in 1..N : Phase1ToPhase2(p))
  /\ WF_vars(\E p \in 1..N : \E m \in sent : ReceivePhase2(p, m))
  /\ WF_vars(\E p \in 1..N : \E v \in Values : DecideOnEstimate(p, v))
  /\ WF_vars(\E p \in 1..N : MoveToChoosing(p))
  /\ WF_vars(\E p \in 1..N : \E v \in Values : ChooseAndDecide(p, v))

Validity ==
  \A p \in 1..N : (decision[p] # Bottom) => \E q \in 1..N : proposed[q] = decision[p]

Agreement ==
  \A p1, p2 \in 1..N : (decision[p1] # Bottom /\ decision[p2] # Bottom) => decision[p1] = decision[p2]

Termination ==
  \A p \in 1..N : (loc[p] = "crashed" \/ decision[p] # Bottom) ~> (loc[p] = "crashed" \/ decision[p] # Bottom)

\* The maximum value is guaranteed only when enough processes actually proposed it.
ConditionC1 == \E q \in 1..N : proposed[q] = MaxV(Values)
TerminationUnderC1 == Termination /\ (ConditionC1 ~> Termination)

INVARIANT TypeOK
INVARIANT Validity
INVARIANT Agreement
PROPERTY Termination
PROPERTY TerminationUnderC1
====