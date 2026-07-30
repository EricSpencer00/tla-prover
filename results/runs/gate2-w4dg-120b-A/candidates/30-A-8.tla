---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

Processes == 0..(N - 1)
Phases == {"b1", "w1", "prep", "b2", "w2", "done", "crashed", "choosing"}
MsgKinds == {"phase1", "phase2"}

VARIABLES loc, view, propose, est, decide, crashCount, sent, recvd

vars == <<loc, view, propose, est, decide, crashCount, sent, recvd>>

RECURSIVE MaxValue(_)
MaxValue(S) ==
  IF S = {} THEN Bottom
  ELSE LET x == CHOOSE y \in S : TRUE
       IN IF \E z \in S : z > x THEN MaxValue(S \ {x}) ELSE x

TypeOK ==
  /\ loc \in [Processes -> Phases]
  /\ view \in [Processes -> [Processes -> Values \cup {Bottom}]]
  /\ propose \in [Processes -> Values]
  /\ est \in [Processes -> Values \cup {Bottom}]
  /\ decide \in [Processes -> Values \cup {Bottom}]
  /\ crashCount \in 0..F
  /\ sent \subseteq [kind: MsgKinds, val: Values, sender: Processes]
  /\ recvd \in [Processes -> SUBSET [kind: MsgKinds, val: Values, sender: Processes]]

Init ==
  /\ loc = [p \in Processes |-> "b1"]
  /\ view = [p \in Processes |-> [q \in Processes |-> Bottom]]
  /\ propose \in [Processes -> Values]
  /\ est = [p \in Processes |-> Bottom]
  /\ decide = [p \in Processes |-> Bottom]
  /\ crashCount = 0
  /\ sent = {}
  /\ recvd = [p \in Processes |-> {}]

RecvPhase1(p, m) ==
  /\ m.kind = "phase1"
  /\ m.sender \in recvd[p]
  /\ loc[p] = "w1"
  /\ Cardinality({x \in recvd[p] : x.kind = "phase1"}) >= N - T
  /\ est' = [est EXCEPT ![p] = MaxValue({q \in Processes :
                                         view[p][q] # Bottom})]
  /\ loc' = [loc EXCEPT ![p] = "b2"]
  /\ UNCHANGED <<view, propose, decide, crashCount, sent, recvd>>

RecvPhase2(p, m) ==
  /\ m.kind = "phase2"
  /\ m.sender \in recvd[p]
  /\ loc[p] = "w2"
  /\ Cardinality({x \in recvd[p] : x.kind = "phase2" /\ x.val = m.val}) >= N - T
  /\ decide' = [decide EXCEPT ![p] = m.val]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, propose, est, crashCount, sent, recvd>>

BroadcastPhase1(p) ==
  /\ loc[p] = "b1"
  /\ sent' = sent \cup {[kind |-> "phase1", val |-> propose[p], sender |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "w1"]
  /\ UNCHANGED <<view, propose, est, decide, crashCount, recvd>>

BroadcastPhase2(p) ==
  /\ loc[p] = "prep"
  /\ sent' = sent \cup {[kind |-> "phase2", val |-> propose[p], sender |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "w2"]
  /\ UNCHANGED <<view, propose, est, decide, crashCount, recvd>>

Receive(p, m) ==
  /\ m \in sent
  /\ m.sender \notin recvd[p]
  /\ recvd' = [recvd EXCEPT ![p] = recvd[p] \cup {m}]
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ UNCHANGED <<loc, propose, est, decide, crashCount, sent>>

Prepare(p) ==
  /\ loc[p] = "w1"
  /\ loc' = [loc EXCEPT ![p] = "prep"]
  /\ UNCHANGED <<view, propose, est, decide, crashCount, sent, recvd>>

Choose(p) ==
  /\ loc[p] = "choosing"
  /\ Cardinality({q \in Processes : view[p][q] # Bottom}) = N
  /\ \E v \in {view[p][q] : q \in Processes} :
       /\ v # Bottom
       /\ decide' = [decide EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, propose, est, crashCount, sent, recvd>>

MoveToChoosing(p) ==
  /\ loc[p] = "w2"
  /\ \A v \in Values : Cardinality({x \in recvd[p] : x.kind = "phase2" /\ x.val = v})
                          < N - T
  /\ Cardinality({q \in Processes : view[p][q] # Bottom}) = N
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, propose, est, decide, crashCount, sent, recvd>>

Crash(p) ==
  /\ loc[p] \notin {"crashed", "done"}
  /\ crashCount < F
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashCount' = crashCount + 1
  /\ UNCHANGED <<view, propose, est, decide, sent, recvd>>

Next ==
  \/ \E p \in Processes : BroadcastPhase1(p) \/ BroadcastPhase2(p) \/ Prepare(p)
       \/ Choose(p) \/ MoveToChoosing(p) \/ Crash(p)
  \/ \E p \in Processes, m \in sent : Receive(p, m)
  \/ \E p \in Processes, m \in recvd[p] : RecvPhase1(p, m) \/ RecvPhase2(p, m)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in Processes : BroadcastPhase1(p) \/ BroadcastPhase2(p))
        /\ WF_vars(\E p \in Processes : Receive(p, CHOOSE m \in sent : TRUE))
        /\ WF_vars(\E p \in Processes : Prepare(p))
        /\ WF_vars(\E p \in Processes : Choose(p))
        /\ WF_vars(\E p \in Processes : MoveToChoosing(p))

Validity == \A p \in Processes : decide[p] # Bottom => \E q \in Processes : decide[p] = propose[q]

Agreement == \A p, q \in Processes :
               (decide[p] # Bottom /\ decide[q] # Bottom) => decide[p] = decide[q]

Terminated == \A p \in Processes : loc[p] \in {"done", "crashed"}

ConditionC1Precise ==
  LET mx == MaxValue({propose[p] : p \in Processes})
  IN Cardinality({p \in Processes : propose[p] = mx}) >= F + 1

ConditionalTermination == ConditionC1Precise => Terminated

====