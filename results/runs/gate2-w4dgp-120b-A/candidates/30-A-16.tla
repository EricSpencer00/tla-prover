---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME N \in Nat /\ T \in Nat /\ F \in Nat /\ N > 0 /\ 2 * T < N /\ F <= T /\ Bottom \notin Values

Processes == 1..N
Senders == 1..N
Phases == {"bc1", "wait1", "prep", "bc2", "wait2", "done", "crashed", "choose"}
Types == {"phase1", "phase2"}

Messages == [type : Types, value : Values, sender : Senders]
Phase2Messages == [type : {"phase2"}, value : Values, sender : Senders, estimate : Values]

MaxA(a) == a[1]
MaxB(b) == IF \A x \in DOMAIN b : b[x] = Bottom THEN Bottom ELSE LET m == CHOOSE x \in DOMAIN b : \A y \in DOMAIN b : b[y] <= b[x] IN b[m]

RECURSIVE MaxSet(_, _)
MaxSet(S, f) ==
  IF S = {} THEN Bottom
  ELSE LET x == CHOOSE y \in S : TRUE IN
       LET r == MaxSet(S \ {x}, f) IN IF r = Bottom \/ f[x] > r THEN f[x] ELSE r

AllSent(m) == \A p \in Processes : \E m2 \in m : m2.sender = p

VARIABLES loc, view, prop, est, decision, crashes, sent, recv
vars == <<loc, view, prop, est, decision, crashes, sent, recv>>

TypeOK ==
  /\ loc \in [Processes -> Phases]
  /\ view \in [Processes -> [Processes -> Values \cup {Bottom}]]
  /\ prop \in [Processes -> Values]
  /\ est \in [Processes -> Values \cup {Bottom}]
  /\ decision \in [Processes -> Values \cup {Bottom}]
  /\ crashes \in 0..F
  /\ sent \subseteq Messages
  /\ recv \subseteq Messages

Init ==
  /\ loc = [p \in Processes |-> "bc1"]
  /\ view = [p \in Processes |-> [q \in Processes |-> Bottom]]
  /\ prop \in [Processes -> Values]
  /\ est = [p \in Processes |-> Bottom]
  /\ decision = [p \in Processes |-> Bottom]
  /\ crashes = 0
  /\ sent = {}
  /\ recv = {}

MaxVal == MaxSet(Processes, prop)

BroadcastPhase1(p) ==
  /\ loc[p] = "bc1"
  /\ sent' = sent \cup {[type |-> "phase1", value |-> prop[p], sender |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "wait1"]
  /\ UNCHANGED <<view, prop, est, decision, crashes, sent, recv>>

ReceivePhase1(p, m) ==
  /\ loc[p] \in {"wait1", "wait2"}
  /\ m \in sent
  /\ m.type = "phase1"
  /\ view[p][m.sender] = Bottom
  /\ view' = [view EXCEPT ![p][m.sender] = m.value]
  /\ recv' = recv \cup {m}
  /\ UNCHANGED <<loc, prop, est, decision, crashes, sent>>

ComputeEst(p) ==
  /\ loc[p] = "wait1"
  /\ Cardinality({q \in Processes : view[p][q] # Bottom}) >= N - T
  /\ est' = [est EXCEPT ![p] = MaxA(view[p])]
  /\ loc' = [loc EXCEPT ![p] = "bc2"]
  /\ UNCHANGED <<view, prop, decision, crashes, sent, recv>>

BroadcastPhase2(p) ==
  /\ loc[p] = "bc2"
  /\ sent' = sent \cup {[type |-> "phase2", value |-> prop[p], sender |-> p, estimate |-> est[p]]}
  /\ loc' = [loc EXCEPT ![p] = "wait2"]
  /\ UNCHANGED <<view, prop, est, decision, crashes, recv>>

Decide(p) ==
  /\ loc[p] = "wait2"
  /\ \E m \in recv : m.type = "phase2" /\ m.estimate = est[p]
  /\ Cardinality({m \in recv : m.type = "phase2" /\ m.estimate = est[p]}) >= N - T
  /\ decision' = [decision EXCEPT ![p] = est[p]]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashes, sent, recv>>

Choose(p) ==
  /\ loc[p] = "wait2"
  /\ AllSent(recv)
  /\ Cardinality({m \in recv : m.type = "phase2" /\ m.estimate = est[p]}) < N - T
  /\ loc' = [loc EXCEPT ![p] = "choose"]
  /\ UNCHANGED <<view, prop, est, decision, crashes, sent, recv>>

DecideChosen(p) ==
  /\ loc[p] = "choose"
  /\ \E q \in Processes : view[p][q] # Bottom
  /\ decision' = [decision EXCEPT ![p] = MaxB(view[p])]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashes, sent, recv>>

Crash(p) ==
  /\ loc[p] \notin {"crashed", "done"}
  /\ crashes < F
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashes' = crashes + 1
  /\ UNCHANGED <<view, prop, est, decision, sent, recv>>

Next ==
  \/ \E p \in Processes : BroadcastPhase1(p) \/ ComputeEst(p) \/ BroadcastPhase2(p) \/ Decide(p) \/ Choose(p) \/ DecideChosen(p) \/ Crash(p)
  \/ \E p \in Processes, m \in Messages : ReceivePhase1(p, m)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(BroadcastPhase1(1))
  /\ WF_vars(ComputeEst(1))
  /\ WF_vars(BroadcastPhase2(1))
  /\ WF_vars(Decide(1))
  /\ WF_vars(Choose(1))
  /\ WF_vars(DecideChosen(1))

Validity ==
  \A p \in Processes : decision[p] # Bottom => decision[p] \in Values

Agreement ==
  \A p, q \in Processes : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Termination ==
  \A p \in Processes : loc[p] \in {"done", "crashed"}

TerminationC1 ==
  (\A p \in Processes : prop[p] # MaxVal => decision[p] = Bottom) => Termination

====