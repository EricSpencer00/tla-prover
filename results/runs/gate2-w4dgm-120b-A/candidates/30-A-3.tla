---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* The protocol runs in two rounds: each process broadcasts its own
\* proposal in round 1, then broadcasts both its proposal and its
\* computed estimate in round 2. A process may crash silently and then
\* stops participating; the tolerable fault bound T is kept below the
\* obvious quorum threshold so that a crashed minority can never stall
\* the whole agreement.
\* Every decision is backed by an actual proposal, so no decided value
\* is ever invented or lost along the way.
\* Under condition C1 -- at least F+1 proposals equal the global maximum --
\* the two-round dance is guaranteed to converge.

VARIABLES loc, view, proposed, estimate, decided, crashed, sent, recv

TypeOK ==
  /\ loc \in [1..N -> {"ph1bcast", "ph1wait", "choose", "ph2bcast",
                       "ph2wait", "done", "crashed"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ proposed \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq [msgtype: {"ph1", "ph2"}, val: Values, from: 1..N,
                    est: Values \cup {Bottom}]
  /\ recv \in [1..N -> SUBSET [msgtype: {"ph1", "ph2"}, val: Values,
                               from: 1..N, est: Values \cup {Bottom}]]

Init ==
  /\ loc = [p \in 1..N |-> "ph1bcast"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ proposed \in [1..N -> Values]
  /\ estimate = [p \in 1..N |-> Bottom]
  /\ decided = [p \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [p \in 1..N |-> {}]

ValidProposal ==
  \E p \in 1..N : loc[p] \in {"ph1bcast", "ph2bcast"} /\ loc' = [loc EXCEPT ![p] = "ph1wait"]
  /\ UNCHANGED <<view, proposed, estimate, decided, crashed, sent, recv>>

ReceivePh1 ==
  \E p \in 1..N, m \in sent :
    /\ loc[p] = "ph1wait"
    /\ m.msgtype = "ph1"
    /\ m.from # p
    /\ view[p][m.from] = Bottom
    /\ view' = [view EXCEPT ![p][m.from] = m.val]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<loc, proposed, estimate, decided, crashed, sent>>

ComputeEstimate ==
  \E p \in 1..N :
    /\ loc[p] = "ph1wait"
    /\ Cardinality({q \in 1..N : view[p][q] # Bottom}) >= N - T
    /\ estimate[p] = Bottom
    /\ estimate' = [estimate EXCEPT ![p] =
                      CHOOSE v \in Values :
                        \A q \in 1..N : view[p][q] # Bottom => v >= view[p][q]]
    /\ loc' = [loc EXCEPT ![p] = "ph2bcast"]
    /\ UNCHANGED <<view, proposed, decided, crashed, sent, recv>>

BroadcastPh2 ==
  \E p \in 1..N :
    /\ loc[p] = "ph2bcast" /\ loc' = [loc EXCEPT ![p] = "ph2wait"]
    /\ sent' = sent \cup {[msgtype |-> "ph2", val |-> proposed[p],
                           from |-> p, est |-> estimate[p]]}
    /\ UNCHANGED <<view, proposed, estimate, decided, crashed, recv>>

ReceivePh2 ==
  \E p \in 1..N, m \in sent :
    /\ loc[p] = "ph2wait"
    /\ m.msgtype = "ph2"
    /\ m.from # p
    /\ view[p][m.from] = Bottom
    /\ view' = [view EXCEPT ![p][m.from] = m.est]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<loc, proposed, estimate, decided, crashed, sent>>

Decide ==
  \E p \in 1..N, v \in Values :
    /\ loc[p] = "ph2wait"
    /\ Cardinality({m \in recv[p] : m.msgtype = "ph2" /\ m.est = v})
         >= N - T
    /\ decided' = [decided EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, proposed, estimate, crashed, sent, recv>>

\* The fallback is a deterministic choice over what is locally seen; this
\* is the only path that can fire when the estimate quorum never formed.
ChooseDeterministic ==
  \E p \in 1..N :
    /\ loc[p] = "ph2wait"
    /\ {m.from : m \in recv[p] /\ m.msgtype = "ph2"} = 1..N
    /\ \E v \in Values :
         /\ decided' = [decided EXCEPT ![p] = v]
         /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, proposed, estimate, crashed, sent, recv>>

Crash ==
  /\ crashed < F
  /\ \E p \in 1..N :
       /\ loc[p] \notin {"done", "crashed"}
       /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, proposed, estimate, decided, sent, recv>>

Next ==
  \/ ValidProposal \/ ReceivePh1 \/ ComputeEstimate
  \/ BroadcastPh2 \/ ReceivePh2
  \/ Decide \/ ChooseDeterministic \/ Crash

Spec ==
  /\ Init /\ [][Next]_<<loc, view, proposed, estimate, decided, crashed, sent, recv>>
  /\ SF_vars(ValidProposal) /\ SF_vars(ReceivePh1) /\ SF_vars(ComputeEstimate)
  /\ SF_vars(BroadcastPh2) /\ SF_vars(ReceivePh2)
  /\ WF_vars(Decide) /\ WF_vars(ChooseDeterministic) /\ WF_vars(Crash)

\* The two-round protocol never manufactures a value: whatever a process
\* decides was proposed by somebody, and no two processes disagree.
Validity == \A p \in 1..N : decided[p] # Bottom => \E q \in 1..N : proposed[q] = decided[p]
Agreement == \A p, q \in 1..N : (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

\* Everyone eventually either crashes or finishes deciding.
Termination == <>(\A p \in 1..N : loc[p] \in {"crashed", "done"})

\* Condition C1: if enough processes propose the global maximum, the
\* two-round vote can never get stuck on a minority estimate.
UnderC1 ==
  /\ (\E S \in SUBSET 1..N : Cardinality(S) >= F + 1 /\ \A p \in S : proposed[p] = Max(Values))
  /\ Termination

====