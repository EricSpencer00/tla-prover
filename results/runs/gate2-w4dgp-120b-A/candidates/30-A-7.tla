---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES loc, localView, proposed, estimate, decision, crashed, sent, received

vars == <<loc, localView, proposed, estimate, decision, crashed, sent, received>>
Senders == 1..N
Msgs == {1..N}
MsgKinds == {"phase1", "phase2"}

MaxIn(S) == CHOOSE x \in S : \A y \in S : y <= x

TypeOK ==
  /\ loc \in [Msgs -> {"bcast1", "wait1", "prepare", "bcast2",
                       "wait2", "done", "crashed", "choosing"}]
  /\ localView \in [Msgs -> [Msgs -> Values \cup {Bottom}]]
  /\ proposed \in [Msgs -> Values]
  /\ estimate \in [Msgs -> Values \cup {Bottom}]
  /\ decision \in [Msgs -> Values \cup {Bottom}]
  /\ crashed \in 0..T
  /\ sent \subseteq [Msgs -> [kind: MsgKinds, v: Values, s: Senders]]
  /\ received \in [Msgs -> SUBSET [Msgs -> [kind: MsgKinds, v: Values, s: Senders]]]

Init ==
  /\ loc = [m \in Senders |-> "bcast1"]
  /\ localView = [m \in Senders |-> [k \in Senders |-> Bottom]]
  /\ proposed \in [Msgs -> Values]
  /\ estimate = [m \in Senders |-> Bottom]
  /\ decision = [m \in Senders |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ received = [m \in Senders |-> {}]

BroadcastPhase1(m) ==
  /\ loc[m] = "bcast1"
  /\ sent' = sent \cup {[kind |-> "phase1", v |-> proposed[m], s |-> m]}
  /\ loc' = [loc EXCEPT ![m] = "wait1"]
  /\ UNCHANGED <<localView, proposed, estimate, decision, crashed, received>>

RecvPhase1(m, r) ==
  /\ loc[m] = "wait1"
  /\ \E msg \in received[m] : msg.kind = "phase1" /\ msg.s = r /\ msg.v <> Bottom
  /\ UNCHANGED <<loc, sent, decision, estimate, crashed, received>>
  /\ localView' = [localView EXCEPT ![m][r] = (CHOOSE msg \in received[m] :
                                                 msg.kind = "phase1" /\ msg.s = r).v]

GoPrepare(m) ==
  /\ loc[m] = "wait1"
  /\ Cardinality({r \in Senders : localView[m][r] # Bottom}) >= N - T
  /\ estimate' = [estimate EXCEPT ![m] = MaxIn({localView[m][r] : r \in Senders
                                                  /\ localView[m][r] # Bottom})]
  /\ loc' = [loc EXCEPT ![m] = "prepare"]
  /\ UNCHANGED <<localView, proposed, decision, crashed, sent, received>>

BroadcastPhase2(m) ==
  /\ loc[m] = "prepare"
  /\ sent' = sent \cup {[kind |-> "phase2", v |-> proposed[m],
                         s |-> m]}
  /\ loc' = [loc EXCEPT ![m] = "wait2"]
  /\ UNCHANGED <<localView, proposed, estimate, decision, crashed, received>>

RecvPhase2(m, r) ==
  /\ loc[m] = "wait2"
  /\ \E msg \in received[m] : msg.kind = "phase2" /\ msg.s = r /\ msg.v <> Bottom
  /\ UNCHANGED <<loc, sent, decision, estimate, crashed, received>>
  /\ localView' = [localView EXCEPT ![m][r] = (CHOOSE msg \in received[m] :
                                                 msg.kind = "phase2" /\ msg.s = r).v]

Decide(m) ==
  /\ loc[m] = "wait2"
  /\ \E v \in Values :
       Cardinality({r \in Senders : localView[m][r] = v}) >= N - T
         /\ decision' = [decision EXCEPT ![m] = v]
  /\ loc' = [loc EXCEPT ![m] = "done"]
  /\ UNCHANGED <<localView, proposed, estimate, crashed, sent, received>>

ChooseAndDecide(m) ==
  /\ loc[m] = "choosing"
  /\ decision' = [decision EXCEPT ![m] = MaxIn({localView[m][r] : r \in Senders
                                                 /\ localView[m][r] # Bottom})]
  /\ loc' = [loc EXCEPT ![m] = "done"]
  /\ UNCHANGED <<localView, proposed, estimate, crashed, sent, received>>

GoChoose(m) ==
  /\ loc[m] = "wait2"
  /\ Cardinality({r \in Senders : localView[m][r] # Bottom}) = N
  /\ loc' = [loc EXCEPT ![m] = "choosing"]
  /\ UNCHANGED <<localView, proposed, estimate, decision, crashed, sent, received>>

Crash(m) ==
  /\ crashed < T
  /\ loc[m] \notin {"crashed", "done"}
  /\ crashed' = crashed + 1
  /\ loc' = [loc EXCEPT ![m] = "crashed"]
  /\ UNCHANGED <<localView, proposed, estimate, decision, sent, received>>

Deliver(m, r) ==
  \/ RecvPhase1(m, r)
  \/ RecvPhase2(m, r)

Next ==
  \/ \E m \in Senders : BroadcastPhase1(m) \/ BroadcastPhase2(m)
                         \/ GoPrepare(m) \/ Decide(m) \/ GoChoose(m) \/ Crash(m) \/ ChooseAndDecide(m)
  \/ \E m \in Senders, r \in Senders : Deliver(m, r)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Deliver(1, 1))
  /\ WF_vars(Deliver(1, 2))
  /\ WF_vars(Deliver(2, 1))
  /\ WF_vars(Deliver(2, 2))
  /\ WF_vars(Decide(1))
  /\ WF_vars(Decide(2))
  /\ WF_vars(GoChoose(1))
  /\ WF_vars(GoChoose(2))
  /\ WF_vars(ChooseAndDecide(1))
  /\ WF_vars(ChooseAndDecide(2))

Validity ==
  \A m \in Senders : decision[m] # Bottom => decision[m] \in Values

Agreement ==
  \A m, n \in Senders : (decision[m] # Bottom /\ decision[n] # Bottom) => decision[m] = decision[n]

Terminating ==
  \A m \in Senders : (loc[m] = "done" \/ loc[m] = "crashed")

ConditionC1 ==
  \A m \in Senders : (loc[m] = "done" \/ loc[m] = "crashed")
     \/ (MaxIn({proposed[k] : k \in Senders}) \in {proposed[k] : k \in Senders}
         /\ Cardinality({k \in Senders : proposed[k] = MaxIn({proposed[x] : x \in Senders})}) >= F + 1)

====