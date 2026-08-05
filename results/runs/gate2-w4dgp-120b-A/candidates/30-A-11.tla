---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME N \in Nat /\ T \in Nat /\ F \in Nat /\ N > 0 /\ 2 * T < N /\ F <= T

VARIABLES phase, view, prop, estimate, decided, crashed, sent, received

vars == <<phase, view, prop, estimate, decided, crashed, sent, received>>

Procs == 1..N
Msgs == [type: {"ph1", "ph2"}, val: Values \cup {Bottom}, from: Procs, ev: Values \cup {Bottom}]
MaxVals == {w \in Values : \A x \in Values : x <= w}
BottomMsgs == [type |-> "ph1", val |-> Bottom, from |-> 1, ev |-> Bottom]
MaxV == CHOOSE w \in MaxVals : \A x \in Values : x <= w
MaxSenders == {p \in Procs : prop[p] = MaxV}

MaxInView(p) == LET vals == {view[p][q] : q \in Procs} IN CHOOSE w \in vals : \A x \in vals : x <= w

TypeOK ==
  /\ phase \in [Procs -> {"ph1b", "ph1w", "ph2b", "ph2w", "done", "crash", "choose"}]
  /\ view \in [Procs -> [Procs -> Values \cup {Bottom}]]
  /\ prop \in [Procs -> Values]
  /\ estimate \in [Procs -> Values \cup {Bottom}]
  /\ decided \in [Procs -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq Msgs
  /\ received \in [Procs -> SUBSET Msgs]

Init ==
  /\ phase = [p \in Procs |-> "ph1b"]
  /\ view = [p \in Procs |-> [q \in Procs |-> Bottom]]
  /\ prop \in [Procs -> Values]
  /\ estimate = [p \in Procs |-> Bottom]
  /\ decided = [p \in Procs |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ received = [p \in Procs |-> {}]

BroadcastPh1(p) ==
  /\ phase[p] = "ph1b"
  /\ sent' = sent \cup {[type |-> "ph1", val |-> prop[p], from |-> p, ev |-> Bottom]}
  /\ phase' = [phase EXCEPT ![p] = "ph1w"]
  /\ UNCHANGED <<view, prop, estimate, decided, crashed, received>>

ReceivePh1(p, m) ==
  /\ phase[p] = "ph1w"
  /\ m.type = "ph1"
  /\ m \in sent
  /\ m \notin received[p]
  /\ view' = [view EXCEPT ![p][m.from] = m.val]
  /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
  /\ UNCHANGED <<phase, prop, estimate, decided, crashed, sent>>

ComputeEstimate(p) ==
  /\ phase[p] = "ph1w"
  /\ Cardinality({m \in received[p] : m.type = "ph1"}) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = MaxInView(p)]
  /\ phase' = [phase EXCEPT ![p] = "ph2b"]
  /\ UNCHANGED <<view, prop, decided, crashed, sent, received>>

BroadcastPh2(p) ==
  /\ phase[p] = "ph2b"
  /\ sent' = sent \cup {[type |-> "ph2", val |-> prop[p], from |-> p, ev |-> estimate[p]]}
  /\ phase' = [phase EXCEPT ![p] = "ph2w"]
  /\ UNCHANGED <<view, prop, estimate, decided, crashed, received>>

DecidePh2(p, m) ==
  /\ phase[p] = "ph2w"
  /\ m.type = "ph2"
  /\ m \in sent
  /\ m \notin received[p]
  /\ Cardinality({x \in received[p] \cup {m} : x.type = "ph2" /\ x.ev = m.ev}) >= N - T
  /\ decided' = [decided EXCEPT ![p] = m.ev]
  /\ phase' = [phase EXCEPT ![p] = "done"]
  /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
  /\ UNCHANGED <<view, prop, estimate, crashed, sent>>

Choose(p) ==
  /\ phase[p] = "ph2w"
  /\ Cardinality({m \in received[p] : m.type = "ph2"}) = N
  /\ phase' = [phase EXCEPT ![p] = "choose"]
  /\ UNCHANGED <<view, prop, estimate, decided, crashed, sent, received>>

DecideChosen(p) ==
  /\ phase[p] = "choose"
  /\ \E x \in Values : decided' = [decided EXCEPT ![p] = x]
  /\ phase' = [phase EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, received>>

Crash(p) ==
  /\ crashed < F
  /\ crashed' = crashed + 1
  /\ phase' = [phase EXCEPT ![p] = "crash"]
  /\ UNCHANGED <<view, prop, estimate, decided, sent, received>>

Next ==
  \/ \E p \in Procs : BroadcastPh1(p)
  \/ \E p \in Procs, m \in Msgs : ReceivePh1(p, m)
  \/ \E p \in Procs : ComputeEstimate(p)
  \/ \E p \in Procs : BroadcastPh2(p)
  \/ \E p \in Procs, m \in Msgs : DecidePh2(p, m)
  \/ \E p \in Procs : Choose(p)
  \/ \E p \in Procs : DecideChosen(p)
  \/ \E p \in Procs : Crash(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in Procs, m \in Msgs : ReceivePh1(p, m))
  /\ WF_vars(\E p \in Procs : ComputeEstimate(p))
  /\ WF_vars(\E p \in Procs, m \in Msgs : DecidePh2(p, m))
  /\ WF_vars(\E p \in Procs : Choose(p))
  /\ WF_vars(\E p \in Procs : DecideChosen(p))

Validity ==
  \A p \in Procs : decided[p] # Bottom => \E q \in Procs : decided[p] = prop[q]

Agreement ==
  \A p, q \in Procs : (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

Termination ==
  \A p \in Procs : phase[p] \in {"done", "crash"}

CondTermination ==
  (\E p \in Procs : prop[p] = MaxV) ~> (\A p \in Procs : phase[p] \in {"done", "crash"})

====