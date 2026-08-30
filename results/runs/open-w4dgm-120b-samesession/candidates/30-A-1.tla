---- MODULE cbc_max ----
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F, Values, Bottom

Locations == {"broadcast1", "waiting1", "preparing", "broadcast2",
              "waiting2", "done", "crashed", "choosing"}

VARIABLES loc, view, propose, estimate, decided, crashedCount, msgs, recvd
vars == <<loc, view, propose, estimate, decided, crashedCount, msgs, recvd>>

RECURSIVE MaxOf(_)
MaxOf(S) == IF S = {} THEN Bottom
            ELSE LET x == CHOOSE y \in S : TRUE IN
                 IF x > MaxOf(S \ {x}) THEN x ELSE MaxOf(S \ {x})

InitPhases == {"broadcast1", "waiting1", "preparing"}

TypeOK ==
  /\ loc \in [1..N -> Locations]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ propose \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashedCount \in 0..N
  /\ msgs \subseteq [loc : {"phase1", "phase2"}, val : Values, snd : 1..N, est : Values \cup {Bottom}]
  /\ recvd \in [1..N -> SUBSET 1..N]

Init ==
  /\ loc = [n \in 1..N |-> "broadcast1"]
  /\ view = [n \in 1..N |-> [m \in 1..N |-> Bottom]]
  /\ propose \in [1..N -> Values]
  /\ estimate = [n \in 1..N |-> Bottom]
  /\ decided = [n \in 1..N |-> Bottom]
  /\ crashedCount = 0
  /\ msgs = {}
  /\ recvd = [n \in 1..N |-> {}]

BroadcastPhase1(n) ==
  /\ loc[n] = "broadcast1"
  /\ msgs' = msgs \cup {[loc |-> "phase1", val |-> propose[n], snd |-> n, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![n] = "waiting1"]
  /\ UNCHANGED <<view, propose, estimate, decided, crashedCount, recvd>>

ReceivePhase1(n) ==
  /\ loc[n] = "waiting1"
  /\ \E m \in msgs :
       /\ m.loc = "phase1"
       /\ view' = [view EXCEPT ![n][m.snd] = m.val]
       /\ recvd' = [recvd EXCEPT ![n] = recvd[n] \cup {m.snd}]
  /\ UNCHANGED <<loc, propose, estimate, decided, crashedCount, msgs>>

StartPhase2(n) ==
  /\ loc[n] = "waiting1"
  /\ Cardinality(recvd[n]) >= N - T
  /\ estimate' = [estimate EXCEPT ![n] = MaxOf(view[n])]
  /\ loc' = "broadcast2"
  /\ UNCHANGED <<view, propose, decided, crashedCount, msgs, recvd>>

BroadcastPhase2(n) ==
  /\ loc[n] = "broadcast2"
  /\ msgs' = msgs \cup {[loc |-> "phase2", val |-> propose[n], snd |-> n, est |-> estimate[n]]}
  /\ loc' = "waiting2"
  /\ UNCHANGED <<view, propose, estimate, decided, crashedCount, recvd>>

ReceivePhase2(n) ==
  /\ loc[n] = "waiting2"
  /\ \E m \in msgs :
       /\ m.loc = "phase2"
       /\ view' = [view EXCEPT ![n][m.snd] = m.val]
       /\ recvd' = [recvd EXCEPT ![n] = recvd[n] \cup {m.snd}]
  /\ UNCHANGED <<loc, propose, estimate, decided, crashedCount, msgs>>

DecideAtThreshold(n) ==
  /\ loc[n] = "waiting2"
  /\ Cardinality(recvd[n]) >= N - T
  /\ \E v \in Values : Cardinality({m \in msgs : m.loc = "phase2" /\ m.snd \in recvd[n] /\ m.est = v}) >= N - T
  /\ decided' = [decided EXCEPT ![n] = estimate[n]]
  /\ loc' = "done"
  /\ UNCHANGED <<view, propose, estimate, crashedCount, msgs, recvd>>

ChooseArbitrarily(n) ==
  /\ loc[n] = "waiting2"
  /\ recvd[n] = 1..N
  /\ decided' = [decided EXCEPT ![n] = MaxOf(view[n])]
  /\ loc' = "done"
  /\ UNCHANGED <<view, propose, estimate, crashedCount, msgs, recvd>>

Crash(n) ==
  /\ loc[n] \in InitPhases
  /\ crashedCount < F
  /\ loc' = [loc EXCEPT ![n] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED <<view, propose, estimate, decided, msgs, recvd>>

Next ==
  \/ \E n \in 1..N : BroadcastPhase1(n) \/ ReceivePhase1(n) \/ StartPhase2(n)
                    \/ BroadcastPhase2(n) \/ ReceivePhase2(n) \/ DecideAtThreshold(n)
                    \/ ChooseArbitrarily(n) \/ Crash(n)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A n \in 1..N : WF_vars(ReceivePhase1(n))
  /\ \A n \in 1..N : WF_vars(ReceivePhase2(n))
  /\ \A n \in 1..N : WF_vars(StartPhase2(n))
  /\ \A n \in 1..N : WF_vars(DecideAtThreshold(n))
  /\ \A n \in 1..N : WF_vars(ChooseArbitrarily(n))

Validity == \A n \in 1..N : decided[n] # Bottom => \E m \in 1..N : propose[m] = decided[n]

Agreement == \A n1, n2 \in 1..N : (decided[n1] # Bottom /\ decided[n2] # Bottom) => decided[n1] = decided[n2]

Termination == <>(\A n \in 1..N : loc[n] \in {"done", "crashed"})

ConditionalTermination ==
  /\ \A n \in 1..N : (propose[n] = MaxOf(Values) => decided[n] # Bottom)
  /\ \A n \in 1..N : (decided[n] # Bottom => \E m \in 1..N : propose[m] = decided[n])
====