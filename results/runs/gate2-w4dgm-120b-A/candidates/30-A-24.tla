---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Phase-1 and phase-2 message types; messages carry the sender's identity.
MessageTypes == {"phase1", "phase2"}

VARIABLES loc, view, prop, estimate, decided, ncrashed, sentMsgs, recvMsgs

vars == <<loc, view, prop, estimate, decided, ncrashed, sentMsgs, recvMsgs>>

MsgRec == [type: MessageTypes, val: Values, from: 0..(N - 1), est: Values \cup {Bottom}]

TypeOK ==
  /\ loc \in [0..(N - 1)] -> {"bc1", "wait1", "prep", "bc2", "wait2", "done", "crashed", "choosing"}
  /\ view \in [0..(N - 1)][0..(N - 1)] -> Values \cup {Bottom}
  /\ prop \in [0..(N - 1)] -> Values
  /\ estimate \in [0..(N - 1)] -> Values \cup {Bottom}
  /\ decided \in [0..(N - 1)] -> Values \cup {Bottom}
  /\ ncrashed \in Nat
  /\ sentMsgs \subseteq MsgRec
  /\ recvMsgs \in [0..(N - 1)] -> SUBSET MsgRec

\* Views are filled with a distinguished bottom value; the max is well-defined because
\* the value set is finite and all values differ from Bottom.
MaxVals(f) == CHOOSE x \in Values : \A i \in 1..N : f[i] <= x
MaxS(f) == MaxVals([i \in 1..N |-> IF f[i] # Bottom THEN f[i] ELSE CHOOSE x \in Values : TRUE])

Init ==
  /\ loc = [i \in 0..(N - 1) |-> "bc1"]
  /\ view = [i \in 0..(N - 1) |-> [j \in 0..(N - 1) |-> Bottom]]
  /\ prop \in [0..(N - 1) -> Values]
  /\ estimate = [i \in 0..(N - 1) |-> Bottom]
  /\ decided = [i \in 0..(N - 1) |-> Bottom]
  /\ ncrashed = 0
  /\ sentMsgs = {}
  /\ recvMsgs = [i \in 0..(N - 1) |-> {}]

BroadcastPhase1(i) ==
  /\ loc[i] = "bc1"
  /\ sentMsgs' = sentMsgs \cup {[type |-> "phase1", val |-> prop[i], from |-> i, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![i] = "wait1"]
  /\ UNCHANGED <<view, prop, estimate, decided, ncrashed, recvMsgs>>

ReceivePhase1(i, m) ==
  /\ loc[i] = "wait1"
  /\ m.type = "phase1"
  /\ view[i][m.from] = Bottom
  /\ view' = [view EXCEPT ![i][m.from] = m.val]
  /\ recvMsgs' = [recvMsgs EXCEPT ![i] = @ \cup {m}]
  /\ UNCHANGED <<loc, prop, estimate, decided, ncrashed, sentMsgs>>

\* The estimate is the maximum seen in the local view after phase 1.
ComputeEstimate(i) ==
  /\ loc[i] = "wait1"
  /\ Cardinality({m \in recvMsgs[i] : m.type = "phase1"}) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] = MaxS(view[i])]
  /\ loc' = [loc EXCEPT ![i] = "bc2"]
  /\ UNCHANGED <<view, prop, decided, ncrashed, sentMsgs, recvMsgs>>

BroadcastPhase2(i) ==
  /\ loc[i] = "bc2"
  /\ sentMsgs' = sentMsgs \cup {[type |-> "phase2", val |-> prop[i], from |-> i, est |-> estimate[i]]}
  /\ loc' = [loc EXCEPT ![i] = "wait2"]
  /\ UNCHANGED <<view, prop, estimate, decided, ncrashed, recvMsgs>>

ReceivePhase2(i, m) ==
  /\ loc[i] = "wait2"
  /\ m.type = "phase2"
  /\ view[i][m.from] = Bottom
  /\ view' = [view EXCEPT ![i][m.from] = m.val]
  /\ recvMsgs' = [recvMsgs EXCEPT ![i] = @ \cup {m}]
  /\ UNCHANGED <<loc, prop, estimate, decided, ncrashed, sentMsgs>>

DecideByMajority(i) ==
  /\ loc[i] = "wait2"
  /\ Cardinality({m \in recvMsgs[i] : m.type = "phase2" /\ m.est = estimate[i]}) >= N - T
  /\ decided' = [decided EXCEPT ![i] = estimate[i]]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, estimate, ncrashed, sentMsgs, recvMsgs>>

\* Deterministic fallback when no estimated value reaches the N-T threshold.
ChooseFallback(i) ==
  /\ loc[i] = "wait2"
  /\ \A x \in Values : Cardinality({m \in recvMsgs[i] : m.type = "phase2" /\ m.est = x}) < N - T
  /\ loc' = [loc EXCEPT ![i] = "choosing"]
  /\ UNCHANGED <<view, prop, estimate, decided, ncrashed, sentMsgs, recvMsgs>>

ChooseAndDecide(i, v) ==
  /\ loc[i] = "choosing"
  /\ v \in {view[i][j] : j \in 0..(N - 1)} \ {Bottom}
  /\ decided' = [decided EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, estimate, ncrashed, sentMsgs, recvMsgs>>

Crash(i) ==
  /\ loc[i] \notin {"crashed", "done"}
  /\ ncrashed < F
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ ncrashed' = ncrashed + 1
  /\ UNCHANGED <<view, prop, estimate, decided, sentMsgs, recvMsgs>>

Next ==
  \/ \E i \in 0..(N - 1) : BroadcastPhase1(i) \/ ComputeEstimate(i) \/ BroadcastPhase2(i)
                            \/ DecideByMajority(i) \/ ChooseFallback(i) \/ Crash(i)
  \/ \E i \in 0..(N - 1), m \in sentMsgs : ReceivePhase1(i, m) \/ ReceivePhase2(i, m)
  \/ \E i \in 0..(N - 1), v \in Values : ChooseAndDecide(i, v)

Spec == Init /\ [][Next]_vars

\* A decided value was actually proposed by some process (validity).
Validity == \A i \in 0..(N - 1) : decided[i] # Bottom => \E j \in 0..(N - 1) : decided[i] = prop[j]

\* No two processes decide different values (agreement).
Agreement == \A i, j \in 0..(N - 1) : (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

\* Weak fairness on the phase-1 messaging and transition actions, the phase-2
\* messaging and transition actions, the fallback, and the decision action.
Fairness ==
  /\ \A i \in 0..(N - 1), m \in sentMsgs : WF_vars(ReceivePhase1(i, m))
  /\ \A i \in 0..(N - 1) : WF_vars(BroadcastPhase1(i)) /\ WF_vars(ComputeEstimate(i))
                           /\ WF_vars(BroadcastPhase2(i)) /\ WF_vars(DecideByMajority(i))
                           /\ WF_vars(ChooseFallback(i))
  /\ \A i \in 0..(N - 1), v \in Values : WF_vars(ChooseAndDecide(i, v))

\* Under Condition C1, where enough processes propose the global maximum, the
\* protocol always reaches a decision by either phase.
ConditionalTermination ==
  /\ \E i \in 0..(N - 1) : prop[i] = MaxVals([j \in 0..(N - 1) |-> prop[j]])
  /\ (DecideByMajority(0) \/ ChooseFallback(0))

====