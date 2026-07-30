---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

Processes == 1 .. N
MsgTypes == {"phase1", "phase2"}
SentIds == {1 .. (N * N) + N}
LocStates == {"p1bcast", "p1wait", "prepare", "p2bcast", "p2wait", "done", "crashed", "choosing"}

VARIABLES loc, view, proposal, estimate, decision, crashedCount, sent, recv

vars == <<loc, view, proposal, estimate, decision, crashedCount, sent, recv>>

\* A message carries a type, a value, and a sender; phase2 messages also carry the
\* sender's estimated value from phase 1.
Message == [type: MsgTypes, val: Values, sender: Processes, ev: Values \cup {Bottom}, id: SentIds]

TypeOK ==
    /\ loc \in [Processes -> LocStates]
    /\ view \in [Processes -> [Processes -> Values \cup {Bottom}]]
    /\ proposal \in [Processes -> Values]
    /\ estimate \in [Processes -> Values \cup {Bottom}]
    /\ decision \in [Processes -> Values \cup {Bottom}]
    /\ crashedCount \in 0 .. F
    /\ sent \subseteq Message
    /\ recv \in [Processes -> SUBSET SentIds]

Init ==
    /\ loc = [p \in Processes |-> "p1bcast"]
    /\ view = [p \in Processes |-> [q \in Processes |-> Bottom]]
    /\ proposal \in [Processes -> Values]
    /\ estimate = [p \in Processes |-> Bottom]
    /\ decision = [p \in Processes |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ recv = [p \in Processes |-> {}]

BroadcastPhase1(p) ==
    /\ loc[p] = "p1bcast"
    /\ \A m \in sent : m.type # "phase1" \/ m.sender # p
    /\ \E i \in SentIds :
         /\ sent' = sent \cup {[type |-> "phase1", val |-> proposal[p], sender |-> p, ev |-> Bottom, id |-> i]}
    /\ loc' = [loc EXCEPT ![p] = "p1wait"]
    /\ UNCHANGED <<view, proposal, estimate, decision, crashedCount, recv>>

ReceivePhase1(p, m) ==
    /\ loc[p] = "p1wait"
    /\ m \in sent
    /\ m.type = "phase1"
    /\ m.id \notin recv[p]
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m.id}]
    /\ UNCHANGED <<loc, proposal, estimate, decision, crashedCount, sent>>

EstimateValue(p) ==
    /\ loc[p] = "p1wait"
    /\ Cardinality(recv[p]) >= N - T
    /\ estimate' = [estimate EXCEPT ![p] = CHOOSE v \in Values : \A q \in Processes : view[p][q] # Bottom => v >= view[p][q]]
    /\ loc' = [loc EXCEPT ![p] = "p2bcast"]
    /\ UNCHANGED <<view, proposal, decision, crashedCount, sent, recv>>

BroadcastPhase2(p) ==
    /\ loc[p] = "p2bcast"
    /\ \A m \in sent : m.type # "phase2" \/ m.sender # p
    /\ \E i \in SentIds :
         /\ sent' = sent \cup {[type |-> "phase2", val |-> proposal[p], sender |-> p, ev |-> estimate[p], id |-> i]}
    /\ loc' = [loc EXCEPT ![p] = "p2wait"]
    /\ UNCHANGED <<view, proposal, estimate, decision, crashedCount, recv>>

\* Phase2 messages reveal the sender's phase-1 estimate; a quorum on that estimate decides.
DecideWithQuorum(p, v) ==
    /\ loc[p] = "p2wait"
    /\ \E m \in sent :
         /\ m.type = "phase2"
         /\ m.ev = v
         /\ m.id \notin recv[p]
         /\ view' = [view EXCEPT ![p][m.sender] = m.val]
         /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m.id}]
    /\ Cardinality({m \in sent : m.type = "phase2" /\ m.ev = v /\ m.id \in recv[p]}) >= N - T
    /\ decision' = [decision EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<proposal, estimate, crashedCount, sent>>

ChooseArbitrarily(p) ==
    /\ loc[p] = "p2wait"
    /\ Cardinality(recv[p]) = N
    /\ loc' = [loc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<view, proposal, estimate, decision, crashedCount, sent, recv>>

DecideFromChoosing(p) ==
    /\ loc[p] = "choosing"
    /\ \E v \in Values :
         /\ v \in {view[p][q] : q \in Processes}
         /\ decision' = [decision EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, proposal, estimate, crashedCount, sent, recv>>

Crash(p) ==
    /\ loc[p] \notin {"crashed", "done"}
    /\ crashedCount < F
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED <<view, proposal, estimate, decision, sent, recv>>

Next ==
    \/ \E p \in Processes : BroadcastPhase1(p) \/ BroadcastPhase2(p) \/ ChooseArbitrarily(p) \/ DecideFromChoosing(p) \/ Crash(p)
    \/ \E p \in Processes, m \in sent : ReceivePhase1(p, m)
    \/ \E p \in Processes, v \in Values : DecideWithQuorum(p, v)
    \/ \E p \in Processes : EstimateValue(p)

Spec == Init /\ [][Next]_vars
        /\ \A p \in Processes : WF_vars(BroadcastPhase1(p))
                         /\ WF_vars(BroadcastPhase2(p))
                         /\ WF_vars(ReceivePhase1(p, CHOOSE m \in sent : TRUE))
                         /\ WF_vars(DecideWithQuorum(p, CHOOSE v \in Values : TRUE))
                         /\ WF_vars(ChooseArbitrarily(p))
                         /\ WF_vars(DecideFromChoosing(p))

Validity == \A p \in Processes : decision[p] # Bottom => decision[p] \in Values

Agreement == \A p, q \in Processes : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

====