---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES phase, view, prop, estimate, decision, crashed, sent, recv

vars == <<phase, view, prop, estimate, decision, crashed, sent, recv>>

None == "none"
Phases == {"broadcast1", "wait1", "prepare", "broadcast2", "wait2", "done",
           "crashed", "choosing"}
MsgTypes == {"phase1", "phase2"}
MsgIds == [type: MsgTypes, val: Values \cup {Bottom}, sender: 1 .. N, est: Values \cup {Bottom}]

TypeOK ==
  /\ phase \in [1 .. N -> Phases]
  /\ view \in [1 .. N -> [1 .. N -> Values \cup {Bottom}]]
  /\ prop \in [1 .. N -> Values]
  /\ estimate \in [1 .. N -> Values \cup {Bottom}]
  /\ decision \in [1 .. N -> Values \cup {Bottom}]
  /\ crashed \in 0 .. N
  /\ sent \subseteq MsgIds
  /\ recv \subseteq MsgIds

Init ==
  /\ phase = [i \in 1 .. N |-> "broadcast1"]
  /\ view = [i \in 1 .. N |-> [j \in 1 .. N |-> Bottom]]
  /\ prop = [i \in 1 .. N |-> CHOOSE v \in Values : TRUE]
  /\ estimate = [i \in 1 .. N |-> Bottom]
  /\ decision = [i \in 1 .. N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = {}

Broadcast1(i) ==
  /\ phase[i] = "broadcast1"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> prop[i], sender |-> i, est |-> Bottom]}
  /\ phase' = [phase EXCEPT ![i] = "wait1"]
  /\ UNCHANGED <<view, prop, estimate, decision, crashed, recv>>

\* Messages are assumed to be received in any order; recv[] is a set, so matching
\* is by content rather than sequence position.
Receive1(i, m) ==
  /\ phase[i] = "wait1"
  /\ m \in recv
  /\ m.type = "phase1"
  /\ view[i][m.sender] = Bottom
  /\ view' = [view EXCEPT ![i][m.sender] = m.val]
  /\ UNCHANGED <<phase, prop, estimate, decision, crashed, sent, recv>>

\* The estimated value is the maximum seen in the local view, taken only after
\* enough phase-1 messages have arrived.
Estimate(i) ==
  /\ phase[i] = "wait1"
  /\ Cardinality({j \in 1 .. N : view[i][j] # Bottom}) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] = CHOOSE v \in Values :
                    \A w \in Values : (\E j \in 1 .. N : view[i][j] = w) => w <= v]
  /\ phase' = [phase EXCEPT ![i] = "broadcast2"]
  /\ UNCHANGED <<view, prop, decision, crashed, sent, recv>>

Broadcast2(i) ==
  /\ phase[i] = "broadcast2"
  /\ sent' = sent \cup {[type |-> "phase2", val |-> prop[i], sender |-> i,
                         est |-> estimate[i]]}
  /\ phase' = [phase EXCEPT ![i] = "wait2"]
  /\ UNCHANGED <<view, prop, estimate, decision, crashed, recv>>

Receive2(i, m) ==
  /\ phase[i] = "wait2"
  /\ m \in recv
  /\ m.type = "phase2"
  /\ view[i][m.sender] = Bottom
  /\ view' = [view EXCEPT ![i][m.sender] = m.est]
  /\ UNCHANGED <<phase, prop, estimate, decision, crashed, sent, recv>>

DecideFrom1(i) ==
  /\ phase[i] = "wait2"
  /\ decision[i] = Bottom
  /\ Cardinality({j \in 1 .. N : view[i][j] # Bottom /\ view[i][j] = estimate[i]}) >= N - T
  /\ decision' = [decision EXCEPT ![i] = view[i][j]]
  /\ phase' = [phase EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, recv>>

DecideFrom2(i) ==
  /\ phase[i] = "wait2"
  /\ decision[i] = Bottom
  /\ Cardinality({j \in 1 .. N : view[i][j] # Bottom}) = N
  /\ decision' = [decision EXCEPT ![i] = CHOOSE m \in Values : \E j \in 1 .. N : view[i][j] = m]
  /\ phase' = [phase EXCEPT ![i] = "choosing"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, recv>>

Choose(i) ==
  /\ phase[i] = "choosing"
  /\ decision[i] = Bottom
  /\ decision' = [decision EXCEPT ![i] = CHOOSE m \in Values :
                    \E j \in 1 .. N : view[i][j] = m]
  /\ phase' = [phase EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, recv>>

Crash(i) ==
  /\ crashed < F
  /\ phase[i] \notin {"crashed", "done"}
  /\ crashed' = crashed + 1
  /\ phase' = [phase EXCEPT ![i] = "crashed"]
  /\ UNCHANGED <<view, prop, estimate, decision, sent, recv>>

Next ==
  \/ \E i \in 1 .. N: Broadcast1(i)
  \/ \E i \in 1 .. N, m \in recv: Receive1(i, m)
  \/ \E i \in 1 .. N: Estimate(i)
  \/ \E i \in 1 .. N: Broadcast2(i)
  \/ \E i \in 1 .. N, m \in recv: Receive2(i, m)
  \/ \E i \in 1 .. N: DecideFrom1(i)
  \/ \E i \in 1 .. N: DecideFrom2(i)
  \/ \E i \in 1 .. N: Choose(i)
  \/ \E i \in 1 .. N: Crash(i)

\* A crashed process cannot send or receive, so fairness on those actions is
\* guarded on the process being alive; WeakFairness suffices because there is
\* no choice between two enabled actions of the same rank.
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in 1 .. N: (\A m \in recv: WF_vars(Receive1(i, m))
                        /\ WF_vars(Receive2(i, m)) /\ WF_vars(Estimate(i))
                        /\ WF_vars(DecideFrom1(i)) /\ WF_vars(DecideFrom2(i))
                        /\ WF_vars(Choose(i)) /\ WF_vars(Broadcast1(i))
                        /\ WF_vars(Broadcast2(i)))

Validity == \A i \in 1 .. N: decision[i] # Bottom => decision[i] \in Values

Agreement == \A i, j \in 1 .. N: (decision[i] # Bottom /\ decision[j] # Bottom) => decision[i] = decision[j]

Terminate == \A i \in 1 .. N: phase[i] \in {"done", "crashed"}

TerminateC1 == (Cardinality({i \in 1 .. N: prop[i] = CHOOSE x \in Values : TRUE})
                >= F + 1) ~> Terminate

\* The model's own bound on N, T, F, and the value set is left to the cfg file
\* (NOT_SPECIFIED in the description); the spec itself only requires the
\* fundamental feasibility condition on T.
Bound == (2 * T < N) /\ (0 <= F /\ F <= T) /\ (N > 0)
         /\ \A v \in Values : v # Bottom

====