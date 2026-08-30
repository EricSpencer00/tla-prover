------------------------- MODULE cbc_max -------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F, Values, Bottom

VARIABLES loc, view, proposal, estimate, decided, crashed, msgs, rcvd

vars == <<loc, view, proposal, estimate, decided, crashed, msgs, rcvd>>

Locations == {"bc1", "wait1", "prep", "bc2", "wait2", "done", "crashed", "choose"}

Msgs == [type: {"pha1", "pha2"}, val: Values \cup {Bottom}, sender: 1..N, est: Values \cup {Bottom}]

RECURSIVE MaxInSeq(_)
MaxInSeq(s) ==
  IF s = << >> THEN Bottom
  ELSE LET h == Head(s) IN IF h = Bottom THEN MaxInSeq(Tail(s)) ELSE IF MaxInSeq(Tail(s)) = Bottom THEN h ELSE IF h > MaxInSeq(Tail(s)) THEN h ELSE MaxInSeq(Tail(s))

TypeOK ==
  /\ loc \in [1..N -> Locations]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ proposal \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ msgs \subseteq Msgs
  /\ rcvd \in [1..N -> SUBSET Msgs]

Init ==
  /\ loc = [i \in 1..N |-> "bc1"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ proposal \in [1..N -> Values]
  /\ estimate = [i \in 1..N |-> Bottom]
  /\ decided = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ msgs = {}
  /\ rcvd = [i \in 1..N |-> {}]

\* Phase 1: broadcast own proposal to every process.
SendPhase1(i) ==
  /\ loc[i] = "bc1"
  /\ msgs' = msgs \cup {[type |-> "pha1", val |-> proposal[i], sender |-> i, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![i] = "wait1"]
  /\ UNCHANGED <<view, proposal, estimate, decided, crashed, rcvd>>

\* Phase 1: receive proposals and record them in the local view.
RecvPhase1(i, m) ==
  /\ loc[i] = "wait1"
  /\ m.type = "pha1"
  /\ m \notin rcvd[i]
  /\ view' = [view EXCEPT ![i][m.sender] = m.val]
  /\ rcvd' = [rcvd EXCEPT ![i] = @ \cup {m}]
  /\ UNCHANGED <<loc, proposal, estimate, decided, crashed, msgs>>

\* Phase 1: once enough proposals are collected, compute max estimate and move on.
ComputeMax(i) ==
  /\ loc[i] = "wait1"
  /\ Cardinality({m \in rcvd[i] : m.type = "pha1"}) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] = MaxInSeq(Seq(view[i][j] : j \in 1..N))]
  /\ loc' = "bc2"
  /\ UNCHANGED <<view, proposal, decided, crashed, msgs, rcvd>>

\* Phase 2: broadcast own proposal together with own computed estimate.
SendPhase2(i) ==
  /\ loc[i] = "bc2"
  /\ msgs' = msgs \cup {[type |-> "pha2", val |-> proposal[i], sender |-> i, est |-> estimate[i]]}
  /\ loc' = "wait2"
  /\ UNCHANGED <<view, proposal, estimate, decided, crashed, rcvd>>

\* Phase 2: receive votes carrying both a proposal and an estimate.
RecvPhase2(i, m) ==
  /\ loc[i] = "wait2"
  /\ m.type = "pha2"
  /\ m \notin rcvd[i]
  /\ view' = [view EXCEPT ![i][m.sender] = m.val]
  /\ rcvd' = [rcvd EXCEPT ![i] = @ \cup {m}]
  /\ UNCHANGED <<loc, proposal, estimate, decided, crashed, msgs>>

\* Phase 2: if at least N-T votes share an estimated value, adopt it as decision.
DecideByMajority(i) ==
  /\ loc[i] = "wait2"
  /\ \E v \in Values :
       /\ Cardinality({m \in rcvd[i] : m.type = "pha2" /\ m.est = v}) >= N - T
       /\ decided' = [decided EXCEPT ![i] = v]
  /\ loc' = "done"
  /\ UNCHANGED <<view, proposal, estimate, crashed, msgs, rcvd>>

\* Phase 2: if all votes are in but none reach the threshold, fall back to choosing.
FallbackChoose(i) ==
  /\ loc[i] = "wait2"
  /\ Cardinality({m \in rcvd[i] : m.type = "pha2"}) = N
  /\ loc' = "choose"
  /\ UNCHANGED <<view, proposal, estimate, decided, crashed, msgs, rcvd>>

\* Phase 2: deterministically pick any proposal seen in the local view.
ChooseAny(i) ==
  /\ loc[i] = "choose"
  /\ \E v \in Values :
       /\ \E j \in 1..N : view[i][j] = v
       /\ decided' = [decided EXCEPT ![i] = v]
  /\ loc' = "done"
  /\ UNCHANGED <<view, proposal, estimate, crashed, msgs, rcvd>>

\* Any process may crash, up to the bound F, across either phase.
Crash(i) ==
  /\ loc[i] \in {"bc1", "wait1", "prep", "bc2", "wait2", "choose"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, proposal, estimate, decided, msgs, rcvd>>

Next ==
  \/ \E i \in 1..N : SendPhase1(i)
  \/ \E i \in 1..N, m \in msgs : RecvPhase1(i, m)
  \/ \E i \in 1..N : ComputeMax(i)
  \/ \E i \in 1..N : SendPhase2(i)
  \/ \E i \in 1..N, m \in msgs : RecvPhase2(i, m)
  \/ \E i \in 1..N : DecideByMajority(i)
  \/ \E i \in 1..N : FallbackChoose(i)
  \/ \E i \in 1..N : ChooseAny(i)
  \/ \E i \in 1..N : Crash(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E i \in 1..N, m \in msgs : RecvPhase1(i, m))
  /\ WF_vars(\E i \in 1..N : ComputeMax(i))
  /\ WF_vars(\E i \in 1..N, m \in msgs : RecvPhase2(i, m))
  /\ WF_vars(\E i \in 1..N : DecideByMajority(i))
  /\ WF_vars(\E i \in 1..N : FallbackChoose(i))
  /\ WF_vars(\E i \in 1..N : ChooseAny(i))

\* A decided value must have actually been proposed by some process.
Validity ==
  \A i \in 1..N : decided[i] # Bottom => \E j \in 1..N : proposal[j] = decided[i]

\* Two processes that both decide must agree on the decision.
Agreement ==
  \A i, j \in 1..N : (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

\* Every process eventually either crashes or finishes with a decision.
Termination ==
  <>(\A i \in 1..N : loc[i] \in {"crashed", "done"})

\* Conditional termination: the maximum value is decided when F+1 processes propose it.
ConditionC1 ==
  (\E S \in SUBSET 1..N : Cardinality(S) >= F + 1 /\ \A i \in S : proposal[i] = MaxInSeq(Seq(proposal[j] : j \in 1..N)))
    ~> (\A i \in 1..N : decided[i] # Bottom)

=============================================================================