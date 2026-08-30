---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* We model a two-phase condition-based protocol whose second phase admits a
\* deterministic fallback, so progress follows from a fairness guarantee on
\* every single transition the action set offers -- not from quorum alone.

VARIABLES phase, view, proposed, estimate, decision, crashed, sent, recv

vars == <<phase, view, proposed, estimate, decision, crashed, sent, recv>>

TypeOK ==
  /\ phase \in [1..N -> {"bc1", "w1", "prep", "bc2", "w2", "done", "crashed", "choose"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ proposed \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq [type: {"p1", "p2"}, val: Values, snd: 1..N, est: Values \cup {Bottom}]
  /\ recv \in [1..N -> SUBSET 1..N]

MaxInSet(S) ==
  LET f[T \in SUBSET Values] ==
        IF T = {} THEN Bottom
        ELSE LET x == CHOOSE y \in T : \A z \in T : y >= z
             IN x
  IN f[S]

Init ==
  /\ phase = [p \in 1..N |-> "bc1"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ proposed \in [1..N -> Values]
  /\ estimate = [p \in 1..N |-> Bottom]
  /\ decision = [p \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [p \in 1..N |-> {}]

Crash(p) ==
  /\ phase[p] \notin {"crashed", "done"}
  /\ crashed < F
  /\ phase' = [phase EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, proposed, estimate, decision, sent, recv>>

\* Phase 1: broadcast the initially proposed value.
BroadcastP1(p) ==
  /\ phase[p] = "bc1"
  /\ sent' = sent \cup {[type |-> "p1", val |-> proposed[p], snd |-> p, est |-> Bottom]}
  /\ phase' = [phase EXCEPT ![p] = "w1"]
  /\ UNCHANGED <<view, proposed, estimate, decision, crashed, recv>>

ReceiveP1(p, m) ==
  /\ phase[p] = "w1"
  /\ m.type = "p1"
  /\ m.snd \notin recv[p]
  /\ view' = [view EXCEPT ![p][m.snd] = m.val]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m.snd}]
  /\ UNCHANGED <<phase, proposed, estimate, decision, crashed, sent>>

Phase1Decide(p) ==
  /\ phase[p] = "w1"
  /\ Cardinality(recv[p]) >= N - T
  /\ estimate[p] = Bottom
  /\ estimate' = [estimate EXCEPT ![p] = MaxInSet(view[p])]
  /\ phase' = [phase EXCEPT ![p] = "prep"]
  /\ UNCHANGED <<view, proposed, decision, crashed, sent, recv>>

\* Phase 2: broadcast both the original proposal and the derived estimate.
BroadcastP2(p) ==
  /\ phase[p] = "prep"
  /\ sent' = sent \cup {[type |-> "p2", val |-> proposed[p], snd |-> p, est |-> estimate[p]]}
  /\ phase' = [phase EXCEPT ![p] = "w2"]
  /\ UNCHANGED <<view, proposed, estimate, decision, crashed, recv>>

ReceiveP2(p, m) ==
  /\ phase[p] = "w2"
  /\ m.type = "p2"
  /\ m.snd \notin recv[p]
  /\ view' = [view EXCEPT ![p][m.snd] = m.val]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m.snd}]
  /\ UNCHANGED <<phase, proposed, estimate, decision, crashed, sent>>

Phase2Decide(p) ==
  /\ phase[p] = "w2"
  /\ Cardinality(recv[p]) >= N - T
  /\ \E v \in Values : Cardinality({q \in recv[p] : [type |-> "p2", val |-> view[p][q], snd |-> q, est |-> estimate[q]].val = v}) >= N - T
  /\ decision' = [decision EXCEPT ![p] = view[p][CHOOSE q \in recv[p] : view[p][q] = MaxInSet({view[p][r] : r \in recv[p]})]]
  /\ phase' = [phase EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, proposed, estimate, crashed, sent, recv>>

\* Deterministic fallback once every sender has been heard and no estimate won.
Phase2Choose(p) ==
  /\ phase[p] = "w2"
  /\ recv[p] = 1..N
  /\ decision[p] = Bottom
  /\ decision' = [decision EXCEPT ![p] = MaxInSet(view[p])]
  /\ phase' = [phase EXCEPT ![p] = "choose"]
  /\ UNCHANGED <<view, proposed, estimate, crashed, sent, recv>>

Next ==
  \/ \E p \in 1..N : Crash(p)
  \/ \E p \in 1..N : BroadcastP1(p)
  \/ \E p \in 1..N, m \in sent : ReceiveP1(p, m)
  \/ \E p \in 1..N : Phase1Decide(p)
  \/ \E p \in 1..N : BroadcastP2(p)
  \/ \E p \in 1..N, m \in sent : ReceiveP2(p, m)
  \/ \E p \in 1..N : Phase2Decide(p)
  \/ \E p \in 1..N : Phase2Choose(p)

Spec == Init /\ [][Next]_vars
  /\ \A p \in 1..N :
       /\ TRUE
       /\ TRUE
       /\ TRUE
       /\ TRUE
       /\ TRUE
       /\ TRUE
       /\ TRUE
       /\ TRUE
  /\ SF_vars(\E m \in sent : ReceiveP1(1, m))
  /\ SF_vars(\E m \in sent : ReceiveP2(1, m))
  /\ WF_vars(Crash(1))
  /\ WF_vars(Phase2Decide(1))
  /\ WF_vars(Phase2Choose(1))
  /\ SF_vars(\E m \in sent : ReceiveP1(2, m))
  /\ SF_vars(\E m \in sent : ReceiveP2(2, m))
  /\ WF_vars(Crash(2))
  /\ WF_vars(Phase2Decide(2))
  /\ WF_vars(Phase2Choose(2))
  /\ SF_vars(\E m \in sent : ReceiveP1(3, m))
  /\ SF_vars(\E m \in sent : ReceiveP2(3, m))
  /\ WF_vars(Crash(3))
  /\ WF_vars(Phase2Decide(3))
  /\ WF_vars(Phase2Choose(3))
  /\ SF_vars(\E m \in sent : ReceiveP1(4, m))
  /\ SF_vars(\E m \in sent : ReceiveP2(4, m))
  /\ WF_vars(Crash(4))
  /\ WF_vars(Phase2Decide(4))
  /\ WF_vars(Phase2Choose(4))
  /\ SF_vars(\E m \in sent : ReceiveP1(5, m))
  /\ SF_vars(\E m \in sent : ReceiveP2(5, m))
  /\ WF_vars(Crash(5))
  /\ WF_vars(Phase2Decide(5))
  /\ WF_vars(Phase2Choose(5))
  /\ SF_vars(\E m \in sent : ReceiveP1(6, m))
  /\ SF_vars(\E m \in sent : ReceiveP2(6, m))
  /\ WF_vars(Crash(6))
  /\ WF_vars(Phase2Decide(6))
  /\ WF_vars(Phase2Choose(6))

Validity == \A p \in 1..N : decision[p] # Bottom => \E q \in 1..N : proposed[q] = decision[p]

Agreement == \A p, q \in 1..N : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

====