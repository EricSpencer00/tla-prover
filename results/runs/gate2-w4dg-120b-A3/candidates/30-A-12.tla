---- MODULE cbc_max ----
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F, Values, Bottom

Messages == [type: {"phase1", "phase2"}, val: Values, est: Values, sender: 0 .. N - 1]
Phases == {"broadcast1", "waiting1", "prepare", "broadcast2", "waiting2", "done", "crashed", "choosing"}

VARIABLES phase, view, prop, est, decision, crashCount, sent, received

vars == <<phase, view, prop, est, decision, crashCount, sent, received>>

RECURSIVE MaxOver(_, _)
MaxOver(f, S) ==
  IF S = {} THEN Bottom
  ELSE LET x == CHOOSE y \in S : TRUE
           mx == MaxOver(f, S \ {x})
       IN IF f[x] > mx THEN f[x] ELSE mx

Distinct(vs) == \A x \in vs : \A y \in vs : x # y

TypeOK ==
  /\ phase \in [0 .. N - 1 -> Phases]
  /\ view \in [0 .. N - 1 -> [0 .. N - 1 -> Values \cup {Bottom}]]
  /\ prop \in [0 .. N - 1 -> Values]
  /\ est \in [0 .. N - 1 -> Values \cup {Bottom}]
  /\ decision \in [0 .. N - 1 -> Values \cup {Bottom}]
  /\ crashCount \in 0 .. F
  /\ sent \subseteq Messages
  /\ received \in [0 .. N - 1 -> SUBSET Messages]

Init ==
  /\ phase = [p \in 0 .. N - 1 |-> "broadcast1"]
  /\ view = [p \in 0 .. N - 1 |-> [q \in 0 .. N - 1 |-> Bottom]]
  /\ prop \in [0 .. N - 1 -> Values]
  /\ est = [p \in 0 .. N - 1 |-> Bottom]
  /\ decision = [p \in 0 .. N - 1 |-> Bottom]
  /\ crashCount = 0
  /\ sent = {}
  /\ received = [p \in 0 .. N - 1 |-> {}]

BroadcastPhase1(p) ==
  /\ phase[p] = "broadcast1"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> prop[p], est |-> Bottom, sender |-> p]}
  /\ phase' = [phase EXCEPT ![p] = "waiting1"]
  /\ UNCHANGED <<view, prop, est, decision, crashCount, received>>

ReceivePhase1(p, m) ==
  /\ phase[p] = "waiting1"
  /\ m \in sent
  /\ m.type = "phase1"
  /\ view[p][m.sender] = Bottom
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ received' = [received EXCEPT ![p] = @ \cup {m}]
  /\ UNCHANGED <<phase, prop, est, decision, crashCount, sent>>

Prepare(p) ==
  /\ phase[p] = "waiting1"
  /\ Cardinality({m \in received[p] : m.type = "phase1"}) >= N - T
  /\ est' = [est EXCEPT ![p] = MaxOver(view[p], 0 .. N - 1)]
  /\ phase' = [phase EXCEPT ![p] = "prepare"]
  /\ UNCHANGED <<view, prop, decision, crashCount, sent, received>>

BroadcastPhase2(p) ==
  /\ phase[p] = "prepare"
  /\ sent' = sent \cup {[type |-> "phase2", val |-> prop[p], est |-> est[p], sender |-> p]}
  /\ phase' = [phase EXCEPT ![p] = "waiting2"]
  /\ UNCHANGED <<view, prop, est, decision, crashCount, received>>

ReceivePhase2(p, m) ==
  /\ phase[p] = "waiting2"
  /\ m \in sent
  /\ m.type = "phase2"
  /\ view[p][m.sender] = Bottom
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ received' = [received EXCEPT ![p] = @ \cup {m}]
  /\ UNCHANGED <<phase, prop, est, decision, crashCount, sent>>

Decide(p) ==
  /\ phase[p] = "waiting2"
  /\ \E v \in Values :
       /\ Cardinality({m \in received[p] : m.type = "phase2" /\ m.est = v}) >= N - T
       /\ decision' = [decision EXCEPT ![p] = v]
       /\ phase' = [phase EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashCount, sent, received>>

Choose(p) ==
  /\ phase[p] = "waiting2"
  /\ \A m \in received[p] : m.type = "phase2"
  /\ \A v \in Values : Cardinality({m \in received[p] : m.type = "phase2" /\ m.est = v}) < N - T
  /\ phase' = [phase EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, prop, est, decision, crashCount, sent, received>>

Select(p) ==
  /\ phase[p] = "choosing"
  /\ \E v \in Values :
       /\ \E q \in 0 .. N - 1 : view[p][q] = v
       /\ decision' = [decision EXCEPT ![p] = v]
  /\ phase' = [phase EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashCount, sent, received>>

Crash(p) ==
  /\ phase[p] \notin {"done", "crashed"}
  /\ crashCount < F
  /\ phase' = [phase EXCEPT ![p] = "crashed"]
  /\ crashCount' = crashCount + 1
  /\ UNCHANGED <<view, prop, est, decision, sent, received>>

Next ==
  \/ \E p \in 0 .. N - 1 : BroadcastPhase1(p)
  \/ \E p \in 0 .. N - 1, m \in Messages : ReceivePhase1(p, m)
  \/ \E p \in 0 .. N - 1 : Prepare(p)
  \/ \E p \in 0 .. N - 1 : BroadcastPhase2(p)
  \/ \E p \in 0 .. N - 1, m \in Messages : ReceivePhase2(p, m)
  \/ \E p \in 0 .. N - 1 : Decide(p)
  \/ \E p \in 0 .. N - 1 : Choose(p)
  \/ \E p \in 0 .. N - 1 : Select(p)
  \/ \E p \in 0 .. N - 1 : Crash(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E m \in Messages : ReceivePhase1(0, m))
  /\ WF_vars(\E m \in Messages : ReceivePhase2(0, m))
  /\ WF_vars(Prepare(0))
  /\ WF_vars(Decide(0))
  /\ WF_vars(Choose(0))
  /\ WF_vars(Select(0))

Validity ==
  \A p \in 0 .. N - 1 : decision[p] # Bottom => decision[p] \in Values

Agreement ==
  \A p, q \in 0 .. N - 1 : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Termination ==
  \A p \in 0 .. N - 1 : phase[p] \in {"done", "crashed"}

ConditionC1 ==
  LET maxv == MaxOver(prop, 0 .. N - 1)
  IN Cardinality({p \in 0 .. N - 1 : prop[p] = maxv}) >= F + 1

====