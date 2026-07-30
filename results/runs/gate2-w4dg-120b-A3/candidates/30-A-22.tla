---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* The control location of each process in the two-phase protocol.
Locations == {
  "phase1_broadcast", "phase1_wait", "prepare",
  "phase2_broadcast", "phase2_wait", "done", "crashed", "choose"
}

Messages == [
  sender : 1..N,
  type : {"phase1", "phase2"},
  value : Values \cup {Bottom},
  estimate : Values \cup {Bottom}
]

VARIABLES control, view, proposed, estimate, decision, crashedCount, sent, recv

vars == << control, view, proposed, estimate, decision,
            crashedCount, sent, recv >>

RECURSIVE MaxValue(_)
MaxValue(S) == IF S = {} THEN Bottom
              ELSE LET x == CHOOSE y \in S : \A z \in S : z <= y
                   IN x

\* The protocol only makes progress when enough distinct messages have
\* been received, which is what the thresholds below enforce.
EnoughPhase1(v) == Cardinality({p \in 1..N : view[v][p] # Bottom}) >= N - T
EnoughPhase2(v) == Cardinality({p \in 1..N : recv[v][p].type = "phase2" /\ recv[v][p].estimate # Bottom}) >= N - T

TypeOK ==
  /\ control \in [1..N -> Locations]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ proposed \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashedCount \in 0..F
  /\ sent \subseteq Messages
  /\ recv \in [1..N -> [1..N -> Messages \cup {Bottom}]]

Init ==
  /\ control = [p \in 1..N |-> "phase1_broadcast"]
  /\ \E init \in [1..N -> Values] : proposed = init
  /\ view = [v \in 1..N |-> [p \in 1..N |-> Bottom]]
  /\ estimate = [p \in 1..N |-> Bottom]
  /\ decision = [p \in 1..N |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ recv = [v \in 1..N |-> [p \in 1..N |-> Bottom]]

BroadcastPhase1(p) ==
  /\ control[p] = "phase1_broadcast"
  /\ sent' = sent \cup {[sender |-> p, type |-> "phase1", value |-> proposed[p], estimate |-> Bottom]}
  /\ control' = [control EXCEPT ![p] = "phase1_wait"]
  /\ UNCHANGED << view, proposed, estimate, decision, crashedCount, recv >>

ReceivePhase1(v) ==
  /\ control[v] = "phase1_wait"
  /\ \E m \in sent :
       /\ m.type = "phase1"
       /\ recv[v][m.sender] = Bottom
       /\ view' = [view EXCEPT ![v][m.sender] = m.value]
       /\ recv' = [recv EXCEPT ![v][m.sender] = m]
  /\ UNCHANGED << control, proposed, estimate, decision, crashedCount, sent >>

Prepare(v) ==
  /\ control[v] = "phase1_wait"
  /\ EnoughPhase1(v)
  /\ estimate' = [estimate EXCEPT ![v] = MaxValue(view[v])]
  /\ control' = [control EXCEPT ![v] = "phase2_broadcast"]
  /\ UNCHANGED << view, proposed, decision, crashedCount, sent, recv >>

BroadcastPhase2(v) ==
  /\ control[v] = "phase2_broadcast"
  /\ sent' = sent \cup {[sender |-> v, type |-> "phase2", value |-> proposed[v], estimate |-> estimate[v]]}
  /\ control' = [control EXCEPT ![v] = "phase2_wait"]
  /\ UNCHANGED << view, proposed, estimate, decision, crashedCount, recv >>

DecideFromPhase2(v) ==
  /\ control[v] = "phase2_wait"
  /\ \E val \in Values :
       /\ Cardinality({p \in 1..N :
            recv[v][p].type = "phase2" /\ recv[v][p].estimate = val}) >= N - T
       /\ decision' = [decision EXCEPT ![v] = val]
  /\ control' = [control EXCEPT ![v] = "done"]
  /\ UNCHANGED << view, proposed, estimate, crashedCount, sent, recv >>

MoveToChoose(v) ==
  /\ control[v] = "phase2_wait"
  /\ \A p \in 1..N : recv[v][p].type = "phase2"
  /\ control' = [control EXCEPT ![v] = "choose"]
  /\ UNCHANGED << view, proposed, estimate, decision, crashedCount, sent, recv >>

Choose(v) ==
  /\ control[v] = "choose"
  /\ \E val \in Values :
       /\ \E p \in 1..N : view[v][p] = val
       /\ decision' = [decision EXCEPT ![v] = val]
  /\ control' = [control EXCEPT ![v] = "done"]
  /\ UNCHANGED << view, proposed, estimate, crashedCount, sent, recv >>

Crash(p) ==
  /\ control[p] # "crashed"
  /\ crashedCount < F
  /\ control' = [control EXCEPT ![p] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED << view, proposed, estimate, decision, sent, recv >>

Next ==
  \/ \E p \in 1..N : BroadcastPhase1(p)
  \/ \E v \in 1..N : ReceivePhase1(v)
  \/ \E v \in 1..N : Prepare(v)
  \/ \E v \in 1..N : BroadcastPhase2(v)
  \/ \E v \in 1..N : DecideFromPhase2(v)
  \/ \E v \in 1..N : MoveToChoose(v)
  \/ \E v \in 1..N : Choose(v)
  \/ \E p \in 1..N : Crash(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E v \in 1..N : ReceivePhase1(v))
  /\ WF_vars(\E p \in 1..N : Prepare(p))
  /\ WF_vars(\E p \in 1..N : DecideFromPhase2(p))
  /\ WF_vars(\E p \in 1..N : Choose(p))

Validity == \A p \in 1..N : decision[p] # Bottom => (\E q \in 1..N : decision[p] = proposed[q])

Agreement == \A p, q \in 1..N : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Termination == <>(\A p \in 1..N : control[p] \in {"done", "crashed"})

ConditionC1 == (\E c \in Values :
                  Cardinality({p \in 1..N : proposed[p] = MaxValue(Values)}) >= F + 1)
              ~> Termination

====