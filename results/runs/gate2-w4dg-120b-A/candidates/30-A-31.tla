---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  N, T, F, Values, Bottom

ASSUME /\ N \in Nat /\ N > 0
       /\ T \in Nat /\ T >= 0
       /\ 2 * T < N
       /\ F \in Nat /\ F >= 0
       /\ F <= T
       /\ Bottom \notin Values

Msgs == [type : {1, 2}, val : Values, est : Values \cup {Bottom}, from : 1 .. N]

VARIABLES phase, view, prop, est, dec, crashed, sent, recv
vars == <<phase, view, prop, est, dec, crashed, sent, recv>>

TypeOK ==
  /\ phase \in [1 .. N -> {"p1b", "p1w", "prep", "p2b", "p2w", "done", "crashed", "choose"}]
  /\ view \in [1 .. N -> [1 .. N -> Values \cup {Bottom}]]
  /\ prop \in [1 .. N -> Values]
  /\ est \in [1 .. N -> Values \cup {Bottom}]
  /\ dec \in [1 .. N -> Values \cup {Bottom}]
  /\ crashed \in 0 .. N
  /\ sent \subseteq Msgs
  /\ recv \in [1 .. N -> SUBSET Msgs]

\* Phase-1: broadcast proposed values.
Init ==
  /\ phase = [i \in 1 .. N |-> "p1b"]
  /\ view = [i \in 1 .. N |-> [j \in 1 .. N |-> Bottom]]
  /\ prop \in [1 .. N -> Values]
  /\ est = [i \in 1 .. N |-> Bottom]
  /\ dec = [i \in 1 .. N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [i \in 1 .. N |-> {}]

Broadcast(i) ==
  /\ phase[i] \in {"p1b", "rep2b", "p2b"}
  /\ phase' = [phase EXCEPT ![i] = IF phase[i] = "p1b" THEN "p1w"
                                    ELSE IF phase[i] = "rep2b" THEN "p2w"
                                    ELSE IF phase[i] = "p2b" THEN "p2w"
                                    ELSE phase[i]]
  /\ sent' = sent \cup {[type |-> IF phase[i] = "p1b" THEN 1 ELSE 2,
                         val |-> prop[i],
                         est |-> IF phase[i] = "p2b" THEN est[i] ELSE Bottom,
                         from |-> i]}
  /\ UNCHANGED <<view, prop, est, dec, crashed, recv>>

\* Phase-1 receiving: fill the local view with sender values.
RecievePhase1(i, m) ==
  /\ phase[i] = "p1w"
  /\ m \in sent
  /\ m.type = 1
  /\ view[i][m.from] = Bottom
  /\ view' = [view EXCEPT ![i][m.from] = m.val]
  /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
  /\ UNCHANGED <<phase, prop, est, dec, crashed, sent>>

\* After enough phase-1 messages, adopt the maximum as local estimate.
Phase1ToPhase2(i) ==
  /\ phase[i] = "p1w"
  /\ Cardinality({m \in recv[i] : m.type = 1}) >= N - T
  /\ est' = [est EXCEPT ![i] = Max({view[i][j] : j \in 1 .. N})]
  /\ phase' = [phase EXCEPT ![i] = "p2b"]
  /\ UNCHANGED <<view, prop, dec, crashed, sent, recv>>

\* Phase-2 receiving: collect estimated values from others.
RecievePhase2(i, m) ==
  /\ phase[i] = "p2w"
  /\ m \in sent
  /\ m.type = 2
  /\ view[i][m.from] = Bottom
  /\ view' = [view EXCEPT ![i][m.from] = m.est]
  /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
  /\ UNCHANGED <<phase, prop, est, dec, crashed, sent>>

\* When a quorum of phase-2 messages agrees on an estimate, decide it.
DecideOnMajority(i) ==
  /\ phase[i] = "p2w"
  /\ \E v \in Values :
       /\ Cardinality({m \in recv[i] : m.type = 2 /\ m.est = v}) >= N - T
       /\ dec' = [dec EXCEPT ![i] = v]
  /\ phase' = [phase EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

\* If no majority emerges, pick something observed and decide it.
Choose(i) ==
  /\ phase[i] = "p2w"
  /\ \A v \in Values : Cardinality({m \in recv[i] : m.type = 2 /\ m.est = v}) < N - T
  /\ phase' = [phase EXCEPT ![i] = "choose"]
  /\ UNCHANGED <<view, prop, est, dec, crashed, sent, recv>>

DecideByChoosing(i) ==
  /\ phase[i] = "choose"
  /\ \E v \in Values :
       /\ Cardinality({j \in 1 .. N : view[i][j] = v}) >= 1
       /\ dec' = [dec EXCEPT ![i] = v]
  /\ phase' = [phase EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

Crash(i) ==
  /\ phase[i] \notin {"crashed", "done"}
  /\ crashed < F
  /\ phase' = [phase EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, est, dec, sent, recv>>

Next ==
  \/ \E i \in 1 .. N : Broadcast(i) \/ Phase1ToPhase2(i) \/ DecideOnMajority(i)
                         \/ Choose(i) \/ DecideByChoosing(i) \/ Crash(i)
  \/ \E i \in 1 .. N, m \in sent : RecievePhase1(i, m) \/ RecievePhase2(i, m)

Spec == Init /\ [][Next]_vars
        /\ (\A i \in 1 .. N : WF_vars(Broadcast(i)))
        /\ (\A i \in 1 .. N : WF_vars(RecievePhase1(i, [type |-> 1, val |-> CHOOSE prop[N],
                                                      est |-> Bottom, from |-> CHOOSE i \in 1 .. N: TRUE])))
        /\ (\A i \in 1 .. N : WF_vars(RecievePhase2(i, [type |-> 2, val |-> CHOOSE prop[N],
                                                      est |-> Bottom, from |-> CHOOSE i \in 1 .. N: TRUE])))
        /\ (\A i \in 1 .. N : WF_vars(Phase1ToPhase2(i)))
        /\ (\A i \in 1 .. N : WF_vars(DecideOnMajority(i)))
        /\ (\A i \in 1 .. N : WF_vars(Choose(i)))
        /\ (\A i \in 1 .. N : WF_vars(DecideByChoosing(i)))
        /\ (\A i \in 1 .. N : SF_vars(Crash(i)))

Validity == \A i \in 1 .. N : dec[i] # Bottom => \E j \in 1 .. N : prop[j] = dec[i]

Agreement == \A i, j \in 1 .. N : (dec[i] # Bottom /\ dec[j] # Bottom) => dec[i] = dec[j]

Termination == <>(\A i \in 1 .. N : phase[i] \in {"done", "crashed"})

ConditionC1 ==
  LET maxV == CHOOSE v \in Values : \A w \in Values : w <= v
  IN (\A i \in 1 .. N : prop[i] = maxV => i <= F + 1) ~> Termination

Properties == Termination /\ ConditionC1

====