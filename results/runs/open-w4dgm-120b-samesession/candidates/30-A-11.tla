---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

Locations == {"ph1bcast", "ph1wait", "prepare", "ph2bcast", "ph2wait", "done", "crashed", "choosing"}
MsgKinds == {"ph1", "ph2"}
MaxValue == CHOOSE m \in Values : \A o \in Values : o <= m

VARIABLES location, seen, proposal, estimate, decision, crashed, sent, received

vars == <<location, seen, proposal, estimate, decision, crashed, sent, received>>

TypeOK ==
  /\ location \in [1..N -> Locations]
  /\ seen \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ proposal \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq [kind: MsgKinds, val: Values, snd: 1..N, est: Values \cup {Bottom}]
  /\ received \in [1..N -> SUBSET (1..N)]

Init ==
  /\ location = [p \in 1..N |-> "ph1bcast"]
  /\ seen = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ proposal \in [1..N -> Values]
  /\ estimate = [p \in 1..N |-> Bottom]
  /\ decision = [p \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ received = [p \in 1..N |-> {}]

BroadcastPhase1(p) ==
  /\ location[p] = "ph1bcast"
  /\ sent' = sent \cup {[kind |-> "ph1", val |-> proposal[p], snd |-> p, est |-> Bottom]}
  /\ location' = [location EXCEPT ![p] = "ph1wait"]
  /\ UNCHANGED <<seen, proposal, estimate, decision, crashed, received>>

ReceivePhase1(p, m) ==
  /\ location[p] = "ph1wait"
  /\ m.kind = "ph1"
  /\ m.snd \notin received[p]
  /\ seen' = [seen EXCEPT ![p][m.snd] = m.val]
  /\ received' = [received EXCEPT ![p] = @ \cup {m.snd}]
  /\ UNCHANGED <<location, proposal, estimate, decision, crashed, sent>>

ComputeEstimate(p) ==
  /\ location[p] = "ph1wait"
  /\ Cardinality(received[p]) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = \E z \in Values : \A q \in 1..N : seen[p][q] = Bottom => z = Bottom /\ (seen[p][q] # Bottom => seen[p][q] <= z)]
  /\ location' = [location EXCEPT ![p] = "ph2bcast"]
  /\ UNCHANGED <<seen, proposal, decision, crashed, sent, received>>

BroadcastPhase2(p) ==
  /\ location[p] = "ph2bcast"
  /\ sent' = sent \cup {[kind |-> "ph2", val |-> proposal[p], snd |-> p, est |-> estimate[p]]}
  /\ location' = [location EXCEPT ![p] = "ph2wait"]
  /\ UNCHANGED <<seen, proposal, estimate, decision, crashed, received>>

ReceivePhase2(p, m) ==
  /\ location[p] = "ph2wait"
  /\ m.kind = "ph2"
  /\ m.snd \notin received[p]
  /\ seen' = [seen EXCEPT ![p][m.snd] = m.est]
  /\ received' = [received EXCEPT ![p] = @ \cup {m.snd}]
  /\ UNCHANGED <<location, proposal, estimate, decision, crashed, sent>>

DecideByThreshold(p) ==
  /\ location[p] = "ph2wait"
  /\ \E v \in Values : Cardinality({q \in 1..N : seen[p][q] = v}) >= N - T
  /\ decision' = [decision EXCEPT ![p] = CHOOSE v \in Values : Cardinality({q \in 1..N : seen[p][q] = v}) >= N - T]
  /\ location' = [location EXCEPT ![p] = "done"]
  /\ UNCHANGED <<seen, proposal, estimate, crashed, sent, received>>

ChooseArbitrarily(p) ==
  /\ location[p] = "ph2wait"
  /\ Cardinality(received[p]) = N
  /\ \A v \in Values : Cardinality({q \in 1..N : seen[p][q] = v}) < N - T
  /\ decision' = [decision EXCEPT ![p] = CHOOSE q \in 1..N : seen[p][q] # Bottom]
  /\ location' = [location EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<seen, proposal, estimate, crashed, sent, received>>

FinishChoosing(p) ==
  /\ location[p] = "choosing"
  /\ location' = [location EXCEPT ![p] = "done"]
  /\ UNCHANGED <<seen, proposal, estimate, decision, crashed, sent, received>>

Crash(p) ==
  /\ crashed < F
  /\ location[p] \notin {"crashed", "done"}
  /\ location' = [location EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<seen, proposal, estimate, decision, sent, received>>

Next ==
  \/ \E p \in 1..N : BroadcastPhase1(p)
  \/ \E p \in 1..N, m \in sent : ReceivePhase1(p, m)
  \/ \E p \in 1..N : ComputeEstimate(p)
  \/ \E p \in 1..N : BroadcastPhase2(p)
  \/ \E p \in 1..N, m \in sent : ReceivePhase2(p, m)
  \/ \E p \in 1..N : DecideByThreshold(p)
  \/ \E p \in 1..N : ChooseArbitrarily(p)
  \/ \E p \in 1..N : FinishChoosing(p)
  \/ \E p \in 1..N : Crash(p)

Spec == Init /\ [][Next]_vars

Validity == \A p \in 1..N : decision[p] # Bottom => \E q \in 1..N : proposal[q] = decision[p]

Agreement == \A p, q \in 1..N : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]
====