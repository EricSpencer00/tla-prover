---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME 2 * T < N
ASSUME N > 0
ASSUME F >= 0
ASSUME T >= F
ASSUME Bottom \notin Values

VARIABLES loc, view, proposal, estimate, decision, crashed, msgs, rcvd

vars == <<loc, view, proposal, estimate, decision, crashed, msgs, rcvd>>

Locs == {"phase1bcast", "phase1wait", "preparing", "phase2bcast",
         "phase2wait", "done", "crashed", "choosing"}

MsgTypes == {"phase1", "phase2"}

TypeOK ==
  /\ loc \in [1..N -> Locs]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ proposal \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..N
  /\ msgs \subseteq [type: MsgTypes, val: Values, who: 1..N, est: Values \cup {Bottom}]
  /\ rcvd \in [1..N -> SUBSET [type: MsgTypes, val: Values, who: 1..N, est: Values \cup {Bottom}]]

Init ==
  /\ loc = [p \in 1..N |-> "phase1bcast"]
  /\ proposal \in [1..N -> Values]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ estimate = [p \in 1..N |-> Bottom]
  /\ decision = [p \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ msgs = {}
  /\ rcvd = [p \in 1..N |-> {}]

BroadcastPhase1(p) ==
  /\ loc[p] = "phase1bcast"
  /\ msgs' = msgs \cup {[type |-> "phase1", val |-> proposal[p], who |-> p, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![p] = "phase1wait"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, rcvd>>

ReceivePhase1(p, m) ==
  /\ loc[p] = "phase1wait"
  /\ m \in msgs
  /\ m.type = "phase1"
  /\ m.who \notin {q \in 1..N : [type |-> "phase1", val |-> view[p][q], who |-> q, est |-> Bottom] \in rcvd[p]}
  /\ view' = [view EXCEPT ![p][m.who] = m.val]
  /\ rcvd' = [rcvd EXCEPT ![p] = @ \cup {[type |-> "phase1", val |-> m.val, who |-> m.who, est |-> Bottom]}]
  /\ UNCHANGED <<loc, proposal, estimate, decision, crashed, msgs>>

Phase1ToPhase2(p) ==
  /\ loc[p] = "phase1wait"
  /\ Cardinality({m \in rcvd[p] : m.type = "phase1"}) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = CHOOSE v \in Values :
                                \E S \in SUBSET (1..N) :
                                  /\ S # {}
                                  /\ \A q \in S : view[p][q] = v
                                  /\ \A r \in 1..N : view[p][r] # Bottom => view[p][r] <= v]
  /\ loc' = [loc EXCEPT ![p] = "phase2bcast"]
  /\ UNCHANGED <<view, proposal, decision, crashed, msgs, rcvd>>

BroadcastPhase2(p) ==
  /\ loc[p] = "phase2bcast"
  /\ msgs' = msgs \cup {[type |-> "phase2", val |-> proposal[p], who |-> p, est |-> estimate[p]]}
  /\ loc' = [loc EXCEPT ![p] = "phase2wait"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, rcvd>>

ReceivePhase2(p, m) ==
  /\ loc[p] = "phase2wait"
  /\ m \in msgs
  /\ m.type = "phase2"
  /\ view' = [view EXCEPT ![p][m.who] = m.val]
  /\ rcvd' = [rcvd EXCEPT ![p] = @ \cup {[type |-> "phase2", val |-> m.val, who |-> m.who, est |-> m.est]}]
  /\ UNCHANGED <<loc, proposal, estimate, decision, crashed, msgs>>

Decide(p, v) ==
  /\ loc[p] = "phase2wait"
  /\ Cardinality({m \in rcvd[p] : m.type = "phase2" /\ m.est = v}) >= N - T
  /\ decision' = [decision EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, proposal, estimate, crashed, msgs, rcvd>>

MoveToChoosing(p) ==
  /\ loc[p] = "phase2wait"
  /\ \A q \in 1..N : [type |-> "phase2", val |-> proposal[q], who |-> q, est |-> estimate[q]] \in rcvd[p]
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, msgs, rcvd>>

Choose(p, v) ==
  /\ loc[p] = "choosing"
  /\ v \in {view[p][q] : q \in 1..N, view[p][q] # Bottom}
  /\ decision' = [decision EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, proposal, estimate, crashed, msgs, rcvd>>

Crash(p) ==
  /\ loc[p] \notin {"crashed", "done"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, proposal, estimate, decision, msgs, rcvd>>

Next ==
  \/ \E p \in 1..N: BroadcastPhase1(p)
  \/ \E p \in 1..N, m \in msgs: ReceivePhase1(p, m)
  \/ \E p \in 1..N: Phase1ToPhase2(p)
  \/ \E p \in 1..N: BroadcastPhase2(p)
  \/ \E p \in 1..N, m \in msgs: ReceivePhase2(p, m)
  \/ \E p \in 1..N, v \in Values: Decide(p, v)
  \/ \E p \in 1..N: MoveToChoosing(p)
  \/ \E p \in 1..N, v \in Values: Choose(p, v)
  \/ \E p \in 1..N: Crash(p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in 1..N, m \in msgs: ReceivePhase1(p, m))
        /\ WF_vars(\E p \in 1..N: Phase1ToPhase2(p))
        /\ WF_vars(\E p \in 1..N, m \in msgs: ReceivePhase2(p, m))
        /\ WF_vars(\E p \in 1..N: MoveToChoosing(p))
        /\ WF_vars(\E p \in 1..N, v \in Values: Choose(p, v))

Validity == \A p \in 1..N: decision[p] # Bottom => decision[p] \in Values

Agreement == \A p, q \in 1..N: (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Termination ==
  \A p \in 1..N: (loc[p] = "done" \/ loc[p] = "crashed")
  \/ (\E q \in 1..N: loc[q] = "done" \/ loc[q] = "crashed")

MaxVal == CHOOSE v \in Values : \A w \in Values : w <= v

ConditionC1 ==
  Cardinality({p \in 1..N : proposal[p] = MaxVal}) >= F + 1

ConditionalTermination == ConditionC1 => Termination

====