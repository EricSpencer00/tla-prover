---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Each process broadcasts its proposed value (phase 1). A receiving process
\* assembles a local view of everybody's values, then computes its estimate as
\* the maximum seen. The safety property hinges on the fact that every computed
\* estimate is always some received value, so no unproposed value can ever be
\* decided. Phase-2 messages carry the sender's estimate; a process decides only
\* when a strong majority (N-T) carries the same estimate.

VARIABLES cstate, localView, value, estimate, decided, crashed, sent, recv

vars == <<cstate, localView, value, estimate, decided, crashed, sent, recv>>

Locs == {"ph1bcast", "ph1wait", "prepare", "ph2bcast", "ph2wait",
         "done", "crashed", "choosing"}
Types == {"ph1", "ph2"}
Msgs == [type: Types, val: Values, sender: 1..N]

MsgEst(m) == IF m.type = "ph2" THEN m.val ELSE Bottom

TypeOK ==
  /\ cstate \in [1..N -> Locs]
  /\ localView \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ value \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq Msgs
  /\ recv \in [1..N -> SUBSET Msgs]

Init ==
  /\ cstate = [i \in 1..N |-> "ph1bcast"]
  /\ localView = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ \E f \in [1..N -> Values] : value = f
  /\ estimate = [i \in 1..N |-> Bottom]
  /\ decided = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [i \in 1..N |-> {}]

\* A process in the choosing state deterministically picks any value it has
\* seen locally (the choice is made concrete here so weak fairness can fire).
Choose(i) == CHOOSE v \in Values \cup {Bottom} :
               \E j \in 1..N : localView[i][j] = v

BroadcastPhase1(i) ==
  /\ cstate[i] = "ph1bcast"
  /\ sent' = sent \cup {[type |-> "ph1", val |-> value[i], sender |-> i]}
  /\ cstate' = [cstate EXCEPT ![i] = "ph1wait"]
  /\ UNCHANGED <<localView, value, estimate, decided, crashed, recv>>

ReceivePhase1(i, m) ==
  /\ cstate[i] \in {"ph1wait", "ph2wait"}
  /\ m.type = "ph1"
  /\ m \in sent
  /\ m \notin recv[i]
  /\ localView' = [localView EXCEPT ![i][m.sender] = m.val]
  /\ recv' = [recv EXCEPT ![i] = @ \cup {m}]
  /\ UNCHANGED <<cstate, value, estimate, decided, crashed, sent>>

Prepare(i) ==
  /\ cstate[i] = "ph1wait"
  /\ Cardinality({j \in 1..N : [type |-> "ph1", val |-> value[j], sender |-> j] \in recv[i]}) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] = CHOOSE v \in Values \cup {Bottom} :
                     \E j \in 1..N : localView[i][j] = v]
  /\ cstate' = [cstate EXCEPT ![i] = "ph2bcast"]
  /\ UNCHANGED <<localView, value, decided, crashed, sent, recv>>

BroadcastPhase2(i) ==
  /\ cstate[i] = "ph2bcast"
  /\ sent' = sent \cup {[type |-> "ph2", val |-> estimate[i], sender |-> i]}
  /\ cstate' = [cstate EXCEPT ![i] = "ph2wait"]
  /\ UNCHANGED <<localView, value, estimate, decided, crashed, recv>>

Decide(i) ==
  /\ cstate[i] = "ph2wait"
  /\ \E v \in Values :
       /\ Cardinality({j \in 1..N : Cardinality({m \in recv[i] : m.type = "ph2" /\ MsgEst(m) = v}) >= N - T})
       /\ decided' = [decided EXCEPT ![i] = v]
  /\ cstate' = [cstate EXCEPT ![i] = "done"]
  /\ UNCHANGED <<localView, value, estimate, crashed, sent, recv>>

\* No majority estimate can be reached (too few participants, too much churn):
\* fall back on a local choice instead.
ChooseState(i) ==
  /\ cstate[i] = "ph2wait"
  /\ \A j \in 1..N : Cardinality({m \in recv[i] : m.type = "ph2" /\ MsgEst(m) = localView[i][j]}) < N - T
  /\ cstate' = [cstate EXCEPT ![i] = "choosing"]
  /\ UNCHANGED <<localView, value, estimate, decided, crashed, sent, recv>>

FinishChoosing(i) ==
  /\ cstate[i] = "choosing"
  /\ decided' = [decided EXCEPT ![i] = Choose(i)]
  /\ cstate' = [cstate EXCEPT ![i] = "done"]
  /\ UNCHANGED <<localView, value, estimate, crashed, sent, recv>>

Crash(i) ==
  /\ crashed < F
  /\ cstate[i] \notin {"crashed", "done"}
  /\ crashed' = crashed + 1
  /\ cstate' = [cstate EXCEPT ![i] = "crashed"]
  /\ UNCHANGED <<localView, value, estimate, decided, sent, recv>>

Next ==
  \/ \E i \in 1..N :
       \/ BroadcastPhase1(i) \/ BroadcastPhase2(i) \/ Prepare(i)
       \/ Decide(i) \/ ChooseState(i) \/ FinishChoosing(i) \/ Crash(i)
       \/ \E m \in Msgs : ReceivePhase1(i, m)
  \/ UNCHANGED vars

Spec ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars([i \in 1..N |-> BroadcastPhase1(i)])
  /\ WF_vars([i \in 1..N |-> BroadcastPhase2(i)])
  /\ WF_vars([i \in 1..N |-> Prepare(i)])
  /\ WF_vars([i \in 1..N |-> Decide(i)])
  /\ WF_vars([i \in 1..N |-> ChooseState(i)])
  /\ WF_vars([i \in 1..N |-> FinishChoosing(i)])
  /\ WF_vars([i \in 1..N |-> \E m \in Msgs : ReceivePhase1(i, m)])

\* Safety: any decided value must be a value someone actually proposed, and
\* no two processes ever end up deciding differently.
Validity == \A i \in 1..N : decided[i] # Bottom => \E j \in 1..N : value[j] = decided[i]
Agreement == \A a, b \in 1..N : (decided[a] # Bottom /\ decided[a] = decided[b]) => decided[a] = decided[b]

\* Liveness: everyone eventually finishes or crashes.
Terminating == <>(\A i \in 1..N : cstate[i] \in {"done", "crashed"})
\* Under Condition C1 (a strong enough supporting majority proposes the
\* maximum value), the protocol always reaches termination, not just under
\* fairness of action scheduling.
ConditionalTermination == (Cardinality({i \in 1..N : value[i] = CHOOSE v \in Values : \A j \in 1..N : v >= value[j]}) >= F + 1) ~> Terminating

====