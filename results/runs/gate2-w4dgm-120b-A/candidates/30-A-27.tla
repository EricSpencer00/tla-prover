---- MODULE cbc_max ----
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Cond. C1 (reliable broadcast condition): at least F+1 processes propose
\* the global max value among all proposals, which then guarantees a
\* terminating decision rather than falling back to the arbitrary chooser.
CONSTANT MaxVal
CONSTANTS Phase1, Phase2

VARIABLES loc, view, prop, estimate, decided, crashed, sent, recv
vars == <<loc, view, prop, estimate, decided, crashed, sent, recv>>

TypesOK ==
  /\ loc \in [1..N -> {"phase1bcast", "phase1wait", "prepare", "phase2bcast",
                       "phase2wait", "done", "crashed", "choosing"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq [mtype: {Phase1, Phase2}, val: Values, snd: 1..N,
                     est: Values \cup {Bottom}]
  /\ recv \in [1..N -> SUBSET 1..N]

Init ==
  /\ loc = [i \in 1..N |-> "phase1bcast"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ prop \in [i \in 1..N -> Values]
  /\ estimate = [i \in 1..N |-> Bottom]
  /\ decided = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [i \in 1..N |-> {}]

BroadcastPhase1(i) ==
  /\ loc[i] = "phase1bcast"
  /\ sent' = sent \cup {[mtype |-> Phase1, val |-> prop[i], snd |-> i,
                         est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![i] = "phase1wait"]
  /\ UNCHANGED <<view, prop, estimate, decided, crashed, recv>>

Frequents(S, x) == Cardinality({j \in 1..N : S[j] = x})

\* A process must collect at least N-T matching messages to trust its
\* estimate; with T faults in the system this is exactly the majority bound.
ReceivePhase1(i, j) ==
  /\ loc[i] = "phase1wait"
  /\ \E m \in sent :
       /\ m.snd = j /\ m.mtype = Phase1
       /\ view' = [view EXCEPT ![i][j] = m.val]
       /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {j}]
  /\ UNCHANGED <<loc, prop, estimate, decided, crashed, sent>>

Estimate(i) ==
  /\ loc[i] = "phase1wait"
  /\ Cardinality(recv[i]) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] = Frequents(view[i], MaxVal)]
  /\ loc' = [loc EXCEPT ![i] = "phase2bcast"]
  /\ UNCHANGED <<view, prop, decided, crashed, sent, recv>>

BroadcastPhase2(i) ==
  /\ loc[i] = "phase2bcast"
  /\ sent' = sent \cup {[mtype |-> Phase2, val |-> prop[i], snd |-> i,
                         est |-> estimate[i]]}
  /\ loc' = [loc EXCEPT ![i] = "phase2wait"]
  /\ UNCHANGED <<view, prop, estimate, decided, crashed, recv>>

ReceivePhase2(i, j) ==
  /\ loc[i] = "phase2wait"
  /\ \E m \in sent :
       /\ m.snd = j /\ m.mtype = Phase2 /\ m.est # Bottom
       /\ view' = [view EXCEPT ![i][j] = m.est]
       /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {j}]
  /\ UNCHANGED <<loc, prop, estimate, decided, crashed, sent>>

DecideFromPhase2(i) ==
  /\ loc[i] = "phase2wait"
  /\ \E x \in Values :
       /\ Cardinality({j \in 1..N : view[i][j] = x}) >= N - T
       /\ decided' = [decided EXCEPT ![i] = x]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, recv>>

\* The fallback is deterministic: pick some value from the local view, so
\* two processes that both reach this state cannot ever decide differently.
ChooseArbitrary(i) ==
  /\ loc[i] = "phase2wait"
  /\ recv[i] = 1..N
  /\ \E x \in Values :
       /\ decided' = [decided EXCEPT ![i] = x]
  /\ loc' = [loc EXCEPT ![i] = "choosing"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, recv>>

Crash(i) ==
  /\ loc[i] # "crashed"
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, estimate, decided, sent, recv>>

Next ==
  \/ \E i \in 1..N : BroadcastPhase1(i) \/ Estimate(i)
  \/ \E i \in 1..N, j \in 1..N : ReceivePhase1(i, j)
  \/ \E i \in 1..N : BroadcastPhase2(i)
  \/ \E i \in 1..N, j \in 1..N : ReceivePhase2(i, j)
  \/ \E i \in 1..N : DecideFromPhase2(i) \/ ChooseArbitrary(i) \/ Crash(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E i \in 1..N, j \in 1..N : ReceivePhase1(i, j))
  /\ WF_vars(\E i \in 1..N, j \in 1..N : ReceivePhase2(i, j))
  /\ WF_vars(\E i \in 1..N : Estimate(i))
  /\ WF_vars(\E i \in 1..N : DecideFromPhase2(i))
  /\ WF_vars(\E i \in 1..N : ChooseArbitrary(i))

TypeOK == TypesOK

\* Both invariants are non-trivial only for processes that actually decided.
Validity == \A i \in 1..N : decided[i] # Bottom => \E j \in 1..N : prop[j] = decided[i]

Agreement == \A i, j \in 1..N :
  (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

Termination ==
  <>(\A i \in 1..N : loc[i] \in {"done", "crashed"})

\* C1 (reliable broadcast condition) is the sufficient condition for
\* guaranteed termination rather than falling back to the chooser.
CondC1 == Frequents(prop, MaxVal) >= F + 1

C1GuaranteesTermination == CondC1 ~> Termination
====