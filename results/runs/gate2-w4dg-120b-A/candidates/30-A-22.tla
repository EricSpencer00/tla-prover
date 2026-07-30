---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES loc, view, prop, est, decide, crashed, msgs, recvd

MsgTypes == {"p1", "p2"}

TypeOK ==
  /\ loc \in [1..N -> {"b1", "w1", "prep", "b2", "w2", "done", "crashed", "choose"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ est \in [1..N -> Values]
  /\ decide \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ msgs \subseteq [type: MsgTypes, val: Values, est: Values, snd: 1..N]
  /\ recvd \in [1..N -> SUBSET [type: MsgTypes, val: Values, est: Values, snd: 1..N]]

\* Phase-1 local view: what each process has learned about every other
\* process's proposal.  This is the only state that accumulates knowledge;
\* a phase-2 broadcast and receipt leaves the view unchanged.
ViewOK == \A p \in 1..N : \A q \in 1..N : view[p][q] \in Values \cup {Bottom}

Init ==
  /\ loc = [p \in 1..N |-> "b1"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ prop \in [1..N -> Values]
  /\ est = [p \in 1..N |-> Bottom]
  /\ decide = [p \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ msgs = {}
  /\ recvd = [p \in 1..N |-> {}]

BroadcastPH1(p) ==
  /\ loc[p] = "b1"
  /\ msgs' = msgs \cup {[type |-> "p1", val |-> prop[p], est |-> Bottom, snd |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "w1"]
  /\ UNCHANGED <<view, prop, est, decide, crashed, recvd>>

ReceivePH1(p, m) ==
  /\ loc[p] = "w1"
  /\ m.type = "p1"
  /\ m \notin recvd[p]
  /\ view' = [view EXCEPT ![p][m.snd] = m.val]
  /\ recvd' = [recvd EXCEPT ![p] = recvd[p] \cup {m}]
  /\ UNCHANGED <<loc, prop, est, decide, crashed, msgs>>

\* The estimate is the maximum this process can plausibly deduce from what
\* it has heard, and it is recomputed only once the quorum is reached.
Compute(p) ==
  /\ loc[p] = "w1"
  /\ Cardinality({m \in recvd[p] : m.type = "p1"}) >= N - T
  /\ est' = [est EXCEPT ![p] = CHOOSE v \in Values :
                          \A q \in 1..N : view[p][q] # Bottom => v >= view[p][q]]
  /\ loc' = [loc EXCEPT ![p] = "b2"]
  /\ UNCHANGED <<view, prop, decide, crashed, msgs, recvd>>

BroadcastPH2(p) ==
  /\ loc[p] = "b2"
  /\ msgs' = msgs \cup {[type |-> "p2", val |-> prop[p], est |-> est[p], snd |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "w2"]
  /\ UNCHANGED <<view, prop, est, decide, crashed, recvd>>

\* Decision by majority on the estimated value (a second quorum, on phase 2).
Decide(p, e) ==
  /\ loc[p] = "w2"
  /\ Cardinality({m \in recvd[p] : m.type = "p2" /\ m.est = e}) >= N - T
  /\ decide[p] = Bottom
  /\ decide' = [decide EXCEPT ![p] = e]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, msgs, recvd>>

ReceivePH2(p, m) ==
  /\ loc[p] = "w2"
  /\ m.type = "p2"
  /\ m \notin recvd[p]
  /\ recvd' = [recvd EXCEPT ![p] = recvd[p] \cup {m}]
  /\ UNCHANGED <<view, prop, est, decide, crashed, msgs, loc>>

\* Deterministic tiebreaker: the process simply picks one of the values it
\* saw in its view, so a decision is still always reachable.
Choose(p) ==
  /\ loc[p] = "choose"
  /\ \E e \in Values : decide[p] = Bottom /\ decide' = [decide EXCEPT ![p] = e]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, msgs, recvd>>

MoveToChoose(p) ==
  /\ loc[p] = "w2"
  /\ \A e \in Values : Cardinality({m \in recvd[p] : m.type = "p2" /\ m.est = e}) < N - T
  /\ Cardinality({m \in recvd[p] : m.type = "p2"}) = N
  /\ loc' = [loc EXCEPT ![p] = "choose"]
  /\ UNCHANGED <<view, prop, est, decide, crashed, msgs, recvd>>

Crash(p) ==
  /\ loc[p] \notin {"crashed", "done"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, est, decide, msgs, recvd>>

Next ==
  \/ \E p \in 1..N : BroadcastPH1(p) \/ Compute(p) \/ BroadcastPH2(p)
                     \/ MoveToChoose(p) \/ Choose(p) \/ Crash(p)
  \/ \E p \in 1..N, m \in msgs : ReceivePH1(p, m) \/ ReceivePH2(p, m)
  \/ \E p \in 1..N, e \in Values : Decide(p, e)

\* Strong fairness is needed on reception and on the compute/decide branch
\* each time, because a process whose view is stuck can otherwise starve.
Spec ==
  /\ Init
  /\ [][Next]_<<loc, view, prop, est, decide, crashed, msgs, recvd>>
  /\ WF_vars(\E m \in msgs : ReceivePH1(1, m))
  /\ WF_vars(\E m \in msgs : ReceivePH2(1, m))
  /\ SF_vars(Compute(1))
  /\ SF_vars(Decide(1, CHOOSE p \in 1..N : est[p]))
  /\ WF_vars(Choose(1))

Validity ==
  \A p \in 1..N : decide[p] # Bottom => \E q \in 1..N : prop[q] = decide[p]

Agreement ==
  \A p, q \in 1..N : (decide[p] # Bottom /\ decide[q] # Bottom) => decide[p] = decide[q]

Termination ==
  \A p \in 1..N : (loc[p] \in {"done", "crashed"})

ConditionC1 ==
  \E p \in 1..N :
    /\ Cardinality({q \in 1..N : prop[q] = prop[p]}) >= F + 1
    /\ \A r \in 1..N : prop[p] >= prop[r]

Properties == Termination /\ ConditionC1

====