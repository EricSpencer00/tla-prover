---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Processes send phase-1 and phase-2 messages carrying values; the latter
\* also echo the phase-1 estimate. Phase 1 collects enough views to compute
\* the maximum; phase 2 collects enough matching estimates to decide or
\* deterministically choose from the local view.
States == {"bcast1", "wait1", "prep", "bcast2", "wait2", "done", "crashed", "choose"}
MsgTypes == {"p1", "p2"}

VARIABLES loc, view, prop, estimate, decided, crashed, sendLog, recvLog

Msg == [type: MsgTypes, val: Values, snd: 0..(N - 1), est: Values \cup {Bottom}]

TypeOK ==
  /\ loc \in [0..(N - 1) -> States]
  /\ view \in [0..(N - 1) -> [0..(N - 1) -> Values \cup {Bottom}]]
  /\ prop \in [0..(N - 1) -> Values]
  /\ estimate \in [0..(N - 1) -> Values \cup {Bottom}]
  /\ decided \in [0..(N - 1) -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sendLog \subseteq Msg
  /\ recvLog \in [0..(N - 1) -> SUBSET Msg]

Init ==
  /\ loc = [p \in 0..(N - 1) |-> "bcast1"]
  /\ view = [p \in 0..(N - 1) |-> [q \in 0..(N - 1) |-> Bottom]]
  /\ prop \in [0..(N - 1) -> Values]
  /\ estimate = [p \in 0..(N - 1) |-> Bottom]
  /\ decided = [p \in 0..(N - 1) |-> Bottom]
  /\ crashed = 0
  /\ sendLog = {}
  /\ recvLog = [p \in 0..(N - 1) |-> {}]

MaxV(S) == CHOOSE v \in S : \A w \in S : w <= v
Voters(m) == {p \in 0..(N - 1) : \E e \in recvLog[p] : e.snd = m}

Bcast1(p) ==
  /\ loc[p] = "bcast1"
  /\ loc' = [loc EXCEPT ![p] = "wait1"]
  /\ sendLog' = sendLog \cup {[type |-> "p1", val |-> prop[p], snd |-> p, est |-> Bottom]}
  /\ UNCHANGED <<view, prop, estimate, decided, crashed, recvLog>>

\* A message is only applicable to the phase the receiver is currently waiting
\* in; messages from other phases sit in the network until the receiver catches up.
Recv1(p, m) ==
  /\ loc[p] = "wait1"
  /\ m \in recvLog[p]
  /\ m.type = "p1"
  /\ view' = [view EXCEPT ![p][m.snd] = m.val]
  /\ recvLog' = [recvLog EXCEPT ![p] = recvLog[p] \ {m}]
  /\ UNCHANGED <<loc, prop, estimate, decided, crashed, sendLog>>

\* The estimate is the maximum over the received view, which is how the
\* protocol learns about the value space rather than being fixed to prop[p].
Prep(p) ==
  /\ loc[p] = "wait1"
  /\ Cardinality(Voters("p1")) >= (N - T)
  /\ Cardinality({q \in 0..(N - 1) : view[p][q] # Bottom}) >= (N - T)
  /\ estimate' = [estimate EXCEPT ![p] = MaxV({view[p][q] : q \in 0..(N - 1)} \ {Bottom})]
  /\ loc' = [loc EXCEPT ![p] = "bcast2"]
  /\ UNCHANGED <<view, prop, decided, crashed, sendLog, recvLog>>

Bcast2(p) ==
  /\ loc[p] = "bcast2"
  /\ loc' = [loc EXCEPT ![p] = "wait2"]
  /\ sendLog' = sendLog \cup {[type |-> "p2", val |-> prop[p], snd |-> p, est |-> estimate[p]]}
  /\ UNCHANGED <<view, prop, estimate, decided, crashed, recvLog>>

Recv2(p, m) ==
  /\ loc[p] = "wait2"
  /\ m \in recvLog[p]
  /\ m.type = "p2"
  /\ view' = [view EXCEPT ![p][m.snd] = m.val]
  /\ recvLog' = [recvLog EXCEPT ![p] = recvLog[p] \ {m}]
  /\ UNCHANGED <<loc, prop, estimate, decided, crashed, sendLog>>

Decide(p) ==
  /\ loc[p] = "wait2"
  /\ \E v \in Values :
       /\ Cardinality({q \in 0..(N - 1) : \E e \in recvLog[p] : e.type = "p2" /\ e.est = v}) >= (N - T)
       /\ decided' = [decided EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sendLog, recvLog>>

\* A process may still finish even though no estimate reached the threshold,
\* by picking a value it has already seen in its own view.
Choose(p) ==
  /\ loc[p] = "wait2"
  /\ \A q \in 0..(N - 1) : view[p][q] # Bottom
  /\ Cardinality({q \in 0..(N - 1) : view[p][q] # Bottom}) = N
  /\ decided' = [decided EXCEPT ![p] = CHOOSE v \in {view[p][q] : q \in 0..(N - 1)} : TRUE]
  /\ loc' = [loc EXCEPT ![p] = "choose"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sendLog, recvLog>>

Crash(p) ==
  /\ loc[p] \notin {"done", "crashed"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, estimate, decided, sendLog, recvLog>>

Receive(p, m) == Recv1(p, m) \/ Recv2(p, m)

Next ==
  \/ \E m \in sendLog : Receive(0, m) \/ Receive(1, m) \/ Receive(2, m)
  \/ \E p \in 0..(N - 1) : Bcast1(p) \/ Prep(p) \/ Bcast2(p) \/ Decide(p) \/ Choose(p) \/ Crash(p)

Spec ==
  /\ Init
  /\ [][Next]_<<loc, view, prop, estimate, decided, crashed, sendLog, recvLog>>
  /\ WF_Vars(\E p \in 0..(N - 1) : Bcast1(p))
  /\ WF_Vars(\E p \in 0..(N - 1) : Recv1(p, [type |-> "p1", val |-> CHOOSE x \in Values : TRUE, snd |-> 0, est |-> Bottom]))
  /\ WF_Vars(\E p \in 0..(N - 1) : Prep(p))
  /\ WF_Vars(\E p \in 0..(N - 1) : Bcast2(p))
  /\ WF_Vars(\E p \in 0..(N - 1) : Recv2(p, [type |-> "p2", val |-> CHOOSE x \in Values : TRUE, snd |-> 0, est |-> Bottom]))
  /\ WF_Vars(\E p \in 0..(N - 1) : Decide(p) \/ Choose(p))

\* Safety: whatever a process decided, that value was actually proposed.
Validity == \A p \in 0..(N - 1) : decided[p] # Bottom => \E q \in 0..(N - 1) : prop[q] = decided[p]
Agreement == \A p, q \in 0..(N - 1) : (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

\* Liveness: every process either crashes or finishes; with the condition on
\* the initial proposals holding, the protocol always reaches a decision.
Termination == <>(\A p \in 0..(N - 1) : loc[p] \in {"done", "crashed"})
C1 == \E q \in 0..(N - 1) : prop[q] = MaxV(Values)

====