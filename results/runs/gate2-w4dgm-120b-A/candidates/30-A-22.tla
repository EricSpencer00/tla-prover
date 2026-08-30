---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES phase, view, prop, estimate, decided, crashed, sent, recvd

TypeOK ==
  /\ phase \in [1..N -> {"ph1broadcast", "ph1wait", "prepare", "ph2broadcast", "ph2wait", "done", "crashed", "choosing"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..N
  /\ sent \subseteq [type: {"ph1", "ph2"}, val: Values, snd: 1..N, est: Values \cup {Bottom}]
  /\ recvd \in [1..N -> SUBSET 1..N]

Init ==
  /\ phase = [p \in 1..N |-> "ph1broadcast"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ prop \in [1..N -> Values]
  /\ estimate = [p \in 1..N |-> Bottom]
  /\ decided = [p \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recvd = [p \in 1..N |-> {}]

\* Phase 1: broadcast a proposed value and collect N-T distinct phase-1 messages.
Broadcast1(p) ==
  /\ phase[p] = "ph1broadcast"
  /\ sent' = sent \cup {[type |-> "ph1", val |-> prop[p], snd |-> p, est |-> Bottom]}
  /\ phase' = [phase EXCEPT ![p] = "ph1wait"]
  /\ recvd' = [recvd EXCEPT ![p] = {}]
  /\ UNCHANGED <<view, prop, estimate, decided, crashed>>

Receive1(p, m) ==
  /\ phase[p] = "ph1wait"
  /\ m.type = "ph1"
  /\ p \notin recvd[p]
  /\ view' = [view EXCEPT ![p][m.snd] = m.val]
  /\ recvd' = [recvd EXCEPT ![p] = @ \cup {m.snd}]
  /\ UNCHANGED <<phase, prop, estimate, decided, crashed, sent>>

\* Once enough messages have arrived, locally compute the maximum as the estimate
\* and move to the second phase.
WaitToPrepare(p) ==
  /\ phase[p] = "ph1wait"
  /\ Cardinality(recvd[p]) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = CHOOSE v \in Values :
                     \A q \in 1..N : (view[p][q] # Bottom) => (v >= view[p][q])]
  /\ phase' = [phase EXCEPT ![p] = "prepare"]
  /\ UNCHANGED <<view, prop, decided, crashed, sent, recvd>>

\* Phase 2: broadcast the estimate and collect N-T matching estimates.
Broadcast2(p) ==
  /\ phase[p] \in {"prepare", "ph2wait"}
  /\ sent' = sent \cup {[type |-> "ph2", val |-> prop[p], snd |-> p, est |-> estimate[p]]}
  /\ phase' = [phase EXCEPT ![p] = "ph2wait"]
  /\ recvd' = [recvd EXCEPT ![p] = {}]
  /\ UNCHANGED <<view, prop, estimate, decided, crashed>>

Receive2(p, m) ==
  /\ phase[p] = "ph2wait"
  /\ m.type = "ph2"
  /\ p \notin recvd[p]
  /\ view' = [view EXCEPT ![p][m.snd] = m.est]
  /\ recvd' = [recvd EXCEPT ![p] = @ \cup {m.snd}]
  /\ UNCHANGED <<phase, prop, estimate, decided, crashed, sent>>

DecideByConsensus(p) ==
  /\ phase[p] = "ph2wait"
  /\ \E v \in Values :
       /\ Cardinality({q \in 1..N : view[p][q] = v}) >= N - T
       /\ decided' = [decided EXCEPT ![p] = v]
  /\ phase' = [phase EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, recvd>>

\* If consensus cannot be reached (messages from every sender arrived but no value
\* reached the N-T threshold), fall back to a deterministic local choice.
DecideChoosing(p) ==
  /\ phase[p] = "ph2wait"
  /\ recvd[p] = 1..N
  /\ phase' = [phase EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, prop, estimate, decided, crashed, sent, recvd>>

DecideChosen(p) ==
  /\ phase[p] = "choosing"
  /\ decided' = [decided EXCEPT ![p] = CHOOSE v \in Values : \E q \in 1..N : view[p][q] = v]
  /\ phase' = [phase EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, recvd>>

\* A process may crash silently if the failure budget has not been spent.
Crash(p) ==
  /\ crashed < F
  /\ phase[p] # "crashed"
  /\ phase' = [phase EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, estimate, decided, sent, recvd>>

Next ==
  \/ \E p \in 1..N : Broadcast1(p) \/ WaitToPrepare(p) \/ Broadcast2(p) \/ DecideByConsensus(p)
                        \/ DecideChoosing(p) \/ DecideChosen(p) \/ Crash(p)
  \/ \E p \in 1..N, m \in sent : Receive1(p, m) \/ Receive2(p, m)

\* Phase two is always reachable from every phase-two-waiting state, so weak
\* fairness on the broadcast/reception/consensus/choosing steps guarantees progress.
Spec ==
  /\ Init
  /\ [][Next]_<<phase, view, prop, estimate, decided, crashed, sent, recvd>>
  /\ WF_vars(\E p \in 1..N : Broadcast1(p) \/ Broadcast2(p))
  /\ WF_vars(\E p \in 1..N, m \in sent : Receive1(p, m) \/ Receive2(p, m))
  /\ WF_vars(\E p \in 1..N : WaitToPrepare(p) \/ DecideByConsensus(p)
                        \/ DecideChoosing(p) \/ DecideChosen(p))
  /\ WF_vars(\E p \in 1..N : Crash(p))

\* Every decided value was actually proposed by some process.
Validity == \A p \in 1..N : decided[p] # Bottom => \E q \in 1..N : prop[q] = decided[p]

Agreement == \A p, q \in 1..N : (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

\* The protocol never gets stuck: every process either crashes or finishes.
Termination == <>(\A p \in 1..N : phase[p] \in {"crashed", "done"})

\* Under Condition C1 -- enough processes propose the maximum -- the protocol
\* always terminates.
ConditionC1 == \A p \in 1..N : prop[p] = Max(Values)
ConditionalTermination == ConditionC1 ~> Termination

====