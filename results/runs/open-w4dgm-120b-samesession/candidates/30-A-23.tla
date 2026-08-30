---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* The protocol is two-phase. In phase 1 a process estimates the maximum
\* value it has observed; in phase 2 it decides once enough peers
\* agree on that estimate. SAFETY: validity and agreement of decisions.

VARIABLES loc, observed, proposed, estimate, decided, crashed, sent, received

vars == <<loc, observed, proposed, estimate, decided, crashed, sent, received>>

LOCATIONS == {"broadcasting1", "waiting1", "preparing",
              "broadcasting2", "waiting2", "done", "crashed", "choosing"}

Message == [type: {"phase1", "phase2"}, val: Values \cup {Bottom},
            snd: 0 .. (N - 1), est: Values \cup {Bottom}]

TypeOK ==
  /\ loc \in [0 .. (N - 1) -> LOCATIONS]
  /\ observed \in [0 .. (N - 1) -> [0 .. (N - 1) -> Values \cup {Bottom}]]
  /\ proposed \in [0 .. (N - 1) -> Values]
  /\ estimate \in [0 .. (N - 1) -> Values \cup {Bottom}]
  /\ decided \in [0 .. (N - 1) -> Values \cup {Bottom}]
  /\ crashed \in 0 .. N
  /\ sent \subseteq Message
  /\ received \subseteq Message

Init ==
  /\ loc = [p \in 0 .. (N - 1) |-> "broadcasting1"]
  /\ observed = [p \in 0 .. (N - 1) |-> [q \in 0 .. (N - 1) |-> Bottom]]
  /\ proposed \in [0 .. (N - 1) -> Values]
  /\ estimate = [p \in 0 .. (N - 1) |-> Bottom]
  /\ decided = [p \in 0 .. (N - 1) |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ received = {}

BroadcastPhase1(p) ==
  /\ loc[p] = "broadcasting1"
  /\ loc' = [loc EXCEPT ![p] = "waiting1"]
  /\ sent' = sent \cup {[type |-> "phase1", val |-> proposed[p],
                         snd |-> p, est |-> Bottom]}
  /\ UNCHANGED <<observed, proposed, estimate, decided, crashed, received>>

ReceivePhase1(p, m) ==
  /\ loc[p] \in {"waiting1", "preparing"}
  /\ m \in received
  /\ m.type = "phase1"
  /\ observed' = [observed EXCEPT ![p][m.snd] = m.val]
  /\ UNCHANGED <<loc, proposed, estimate, decided, crashed, sent, received>>

PreparePhase1(p) ==
  /\ loc[p] = "waiting1"
  /\ Cardinality({q \in 0 .. (N - 1) : observed[p][q] # Bottom}) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] =
                    CHOOSE v \in Values :
                      \A q \in 0 .. (N - 1) :
                        (observed[p][q] # Bottom /\ observed[p][q] # v) => observed[p][q] < v]
  /\ loc' = [loc EXCEPT ![p] = "broadcasting2"]
  /\ UNCHANGED <<observed, proposed, decided, crashed, sent, received>>

BroadcastPhase2(p) ==
  /\ loc[p] = "broadcasting2"
  /\ loc' = [loc EXCEPT ![p] = "waiting2"]
  /\ sent' = sent \cup {[type |-> "phase2", val |-> proposed[p],
                         snd |-> p, est |-> estimate[p]]}
  /\ UNCHANGED <<observed, proposed, estimate, decided, crashed, received>>

Decide(p, v) ==
  /\ loc[p] = "waiting2"
  /\ Cardinality({q \in 0 .. (N - 1) :
        \E m \in received : m.type = "phase2" /\ m.snd = q /\ m.est = v}) >= N - T
  /\ decided' = [decided EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<observed, proposed, estimate, crashed, sent, received>>

Choose(p) ==
  /\ loc[p] = "waiting2"
  /\ \A v \in Values :
        Cardinality({q \in 0 .. (N - 1) :
          \E m \in received : m.type = "phase2" /\ m.snd = q /\ m.est = v}) < N - T
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<observed, proposed, estimate, decided, crashed, sent, received>>

Deterministic(p) ==
  /\ loc[p] = "choosing"
  /\ \E v \in Values :
        /\ \A q \in 0 .. (N - 1) : observed[p][q] # Bottom => observed[p][q] <= v
        /\ decided' = [decided EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<observed, proposed, estimate, crashed, sent, received>>

Crash(p) ==
  /\ loc[p] \notin {"crashed", "done"}
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashed' = IF crashed < F THEN crashed + 1 ELSE crashed
  /\ UNCHANGED <<observed, proposed, estimate, decided, sent, received>>

Receive(p, m) == ReceivePhase1(p, m)

Next ==
  \/ \E p \in 0 .. (N - 1) : BroadcastPhase1(p) \/ PreparePhase1(p)
                           \/ BroadcastPhase2(p) \/ Choose(p) \/ Deterministic(p) \/ Crash(p)
  \/ \E p \in 0 .. (N - 1) \E m \in Message : Receive(p, m)
  \/ \E p \in 0 .. (N - 1) \E v \in Values : Decide(p, v)

Spec == Init /\ [][Next]_vars
        /\ (\A p \in 0 .. (N - 1) \E m \in Message : WF_vars(Receive(p, m)))
        /\ (\A p \in 0 .. (N - 1) : WF_vars(PreparePhase1(p)))
        /\ (\A p \in 0 .. (N - 1) : WF_vars(BroadcastPhase2(p)))
        /\ (\A p \in 0 .. (N - 1) : WF_vars(Decide(p, CHOOSE v \in Values : TRUE)))
        /\ (\A p \in 0 .. (N - 1) : WF_vars(Choose(p)))
        /\ (\A p \in 0 .. (N - 1) : SF_vars(Deterministic(p)))

\* Neither decision is invented: each decision value is a proposal.
Validity == \A p \in 0 .. (N - 1) : decided[p] # Bottom => \E q \in 0 .. (N - 1) : decided[p] = proposed[q]

Agreement == \A p, q \in 0 .. (N - 1) : (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

\* Once enough processes propose the maximum, the protocol always ends.
ConditionC1 == (\A p \in 0 .. (N - 1) : decided[p] = Bottom)
                => (\E p \in 0 .. (N - 1) : observed[p][p] = Max(Values))
                /\ ConditionC1

PROPERTIES == ConditionC1

====