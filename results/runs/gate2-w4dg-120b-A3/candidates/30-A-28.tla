---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME N \in Nat /\ N > 0
ASSUME 2 * T < N
ASSUME 0 <= F /\ F <= T
ASSUME Bottom \notin Values

Locs == {"bc1", "w1", "prep", "bc2", "w2", "done", "crash", "choose"}
MsgTypes == {"p1", "p2"}
MsgFields == [ty: MsgTypes, val: Values, from: 1..N, exp: Values]

VARIABLES loc, view, prop, est, dec, crashed, sent, recv

vars == <<loc, view, prop, est, dec, crashed, sent, recv>>

TypeOK ==
  /\ loc \in [1..N -> Locs]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ est \in [1..N -> Values \cup {Bottom}]
  /\ dec \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \in SUBSET MsgFields
  /\ recv \in [1..N -> SUBSET MsgFields]

Init ==
  /\ loc = [p \in 1..N |-> "bc1"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ prop \in [1..N -> Values]
  /\ est = [p \in 1..N |-> Bottom]
  /\ dec = [p \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [p \in 1..N |-> {}]

\* Phase 1: broadcast a proposed value.
BC1(p) ==
  /\ loc[p] = "bc1"
  /\ sent' = sent \cup {[ty |-> "p1", val |-> prop[p], from |-> p, exp |-> Bottom]}
  /\ loc' = [loc EXCEPT ![p] = "w1"]
  /\ UNCHANGED <<view, prop, est, dec, crashed, recv>>

\* Phase 1: receive a message and update the local view.
Rcv1(p) ==
  /\ loc[p] = "w1"
  /\ \E m \in recv[p] :
       /\ m.ty = "p1"
       /\ view' = [view EXCEPT ![p][m.from] = m.val]
  /\ UNCHANGED <<loc, prop, est, dec, crashed, sent, recv>>

\* Phase 1: after receiving from enough senders, estimate the maximum and prepare.
Prep(p) ==
  /\ loc[p] = "w1"
  /\ Cardinality({m \in recv[p] : m.ty = "p1"}) >= N - T
  /\ est' = [est EXCEPT ![p] = Max({v \in Values : \E q \in 1..N : view[p][q] = v})]
  /\ loc' = [loc EXCEPT ![p] = "bc2"]
  /\ UNCHANGED <<view, prop, dec, crashed, sent, recv>>

\* Phase 2: broadcast the proposed and estimated values.
BC2(p) ==
  /\ loc[p] = "bc2"
  /\ sent' = sent \cup {[ty |-> "p2", val |-> prop[p], from |-> p, exp |-> est[p]]}
  /\ loc' = [loc EXCEPT ![p] = "w2"]
  /\ UNCHANGED <<view, prop, est, dec, crashed, recv>>

\* Phase 2: decide when a majority of phase-2 messages agree on the estimate.
Decide(p) ==
  /\ loc[p] = "w2"
  /\ \E v \in Values :
       /\ Cardinality({m \in recv[p] : m.ty = "p2" /\ m.exp = v}) >= N - T
       /\ dec' = [dec EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

\* Phase 2: if no majority emerges, deterministically pick a seen value.
Choose(p) ==
  /\ loc[p] = "w2"
  /\ {m \in recv[p] : m.ty = "p2"} = recv[p]
  /\ \E v \in Values :
       /\ v \in {view[p][q] : q \in 1..N}
       /\ dec' = [dec EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "choose"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

\* A process in the choosing state finalizes its decision.
Decide2(p) ==
  /\ loc[p] = "choose"
  /\ dec' = [dec EXCEPT ![p] = view[p][1]]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

\* The protocol is asynchronous: a process may receive at any time.
RcvAny(p) == Rcv1(p) \/ Choose(p)

\* Any non-crashed process may crash, up to the bound.
Crash(p) ==
  /\ loc[p] \notin {"crash", "done"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![p] = "crash"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, est, dec, sent, recv>>

Next ==
  \/ \E p \in 1..N : BC1(p) \/ BC2(p) \/ Prep(p) \/ Decide(p) \/ Decide2(p) \/ RcvAny(p) \/ Crash(p)
  \/ \E p \in 1..N, q \in 1..N : recv' = [recv EXCEPT ![p] = recv[p] \cup {[ty |-> "p1", val |-> ViewVal(q), from |-> q, exp |-> Bottom]}]

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in 1..N : Rcv1(p))
        /\ WF_vars(\E p \in 1..N : Prep(p))
        /\ WF_vars(\E p \in 1..N : Choose(p))
        /\ WF_vars(\E p \in 1..N : Decide(p))
        /\ WF_vars(\E p \in 1..N : Decide2(p))

\* A decided value was actually proposed by some process.
Validity ==
  \A p \in 1..N : dec[p] # Bottom => \E q \in 1..N : prop[q] = dec[p]

Agreement ==
  \A p, q \in 1..N : (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

Terminate ==
  \A p \in 1..N : (loc[p] = "done" \/ loc[p] = "crash")
  \/ (\E q \in 1..N : loc[q] \in {"done", "crash"})

\* Condition C1: the max is proposed often enough, then the protocol finishes.
Cond1 == (\E p \in 1..N : prop[p] = Max(Values)) ~> (\E q \in 1..N : loc[q] \in {"done", "crash"})

====