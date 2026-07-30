---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

Processes == 1 .. N

MsgTypes == {"p1", "p2"}

VARIABLES phase, view, proposal, estimate, decided, crashCount, sent, received

vars == <<phase, view, proposal, estimate, decided, crashCount, sent, received>>

MsgSpace == [type : MsgTypes, val : Values \cup {Bottom}, from : Processes, est : Values \cup {Bottom}]

MaxOf(S) == CHOOSE x \in S : \A y \in S : y <= x
MaxView(p) == MaxOf({view[p][q] : q \in Processes})

TypeOK ==
  /\ phase \in [Processes -> {"p1b", "p1w", "p2b", "p2w", "done", "crashed", "choose"}]
  /\ view \in [Processes -> [Processes -> Values \cup {Bottom}]]
  /\ proposal \in [Processes -> Values]
  /\ estimate \in [Processes -> Values \cup {Bottom}]
  /\ decided \in [Processes -> Values \cup {Bottom}]
  /\ crashCount \in 0 .. F
  /\ sent \subseteq MsgSpace
  /\ received \in [Processes -> SUBSET MsgSpace]

Init ==
  /\ phase = [p \in Processes |-> "p1b"]
  /\ view = [p \in Processes |-> [q \in Processes |-> Bottom]]
  /\ \E pi \in [Processes -> Values] : proposal = pi
  /\ estimate = [p \in Processes |-> Bottom]
  /\ decided = [p \in Processes |-> Bottom]
  /\ crashCount = 0
  /\ sent = {}
  /\ received = [p \in Processes |-> {}]

BroadcastP1(p) ==
  /\ phase[p] = "p1b"
  /\ sent' = sent \cup {[type |-> "p1", val |-> proposal[p], from |-> p, est |-> Bottom]}
  /\ phase' = [phase EXCEPT ![p] = "p1w"]
  /\ UNCHANGED <<view, proposal, estimate, decided, crashCount, received>>

ReceiveP1(p, m) ==
  /\ phase[p] = "p1w"
  /\ m.type = "p1"
  /\ m.from \in Processes
  /\ m \notin received[p]
  /\ view' = [view EXCEPT ![p][m.from] = m.val]
  /\ received' = [received EXCEPT ![p] = @ \cup {m}]
  /\ UNCHANGED <<phase, proposal, estimate, decided, crashCount, sent>>

ComputeEst(p) ==
  /\ phase[p] = "p1w"
  /\ Cardinality({m.from : m \in received[p] /\ m.type = "p1"}) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = MaxView(p)]
  /\ phase' = [phase EXCEPT ![p] = "p2b"]
  /\ UNCHANGED <<view, proposal, decided, crashCount, sent, received>>

BroadcastP2(p) ==
  /\ phase[p] = "p2b"
  /\ sent' = sent \cup {[type |-> "p2", val |-> proposal[p], from |-> p, est |-> estimate[p]}
  /\ phase' = [phase EXCEPT ![p] = "p2w"]
  /\ UNCHANGED <<view, proposal, estimate, decided, crashCount, received>>

ReceiveP2(p, m) ==
  /\ phase[p] = "p2w"
  /\ m.type = "p2"
  /\ m.from \in Processes
  /\ m \notin received[p]
  /\ view' = [view EXCEPT ![p][m.from] = m.val]
  /\ received' = [received EXCEPT ![p] = @ \cup {m}]
  /\ UNCHANGED <<phase, proposal, estimate, decided, crashCount, sent>>

DecideMatched(p) ==
  /\ phase[p] = "p2w"
  /\ \E v \in Values :
       /\ Cardinality({m.from : m \in received[p] /\ m.type = "p2" /\ m.est = v}) >= N - T
       /\ decided' = [decided EXCEPT ![p] = v]
  /\ phase' = [phase EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, proposal, estimate, crashCount, sent, received>>

Choose(p) ==
  /\ phase[p] = "p2w"
  /\ \A m \in {[type |-> "p2", val |-> v, from |-> q, est |-> Bottom} : q \in Processes, v \in Values] : m \notin received[p]
  /\ \E v \in Values :
       /\ \A q \in Processes : view[p][q] \in {v, Bottom}
       /\ decided' = [decided EXCEPT ![p] = v]
  /\ phase' = [phase EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, proposal, estimate, crashCount, sent, received>>

Crash(p) ==
  /\ phase[p] \notin {"crashed", "done"}
  /\ crashCount < F
  /\ phase' = [phase EXCEPT ![p] = "crashed"]
  /\ crashCount' = crashCount + 1
  /\ UNCHANGED <<view, proposal, estimate, decided, sent, received>>

Next ==
  \/ \E p \in Processes : BroadcastP1(p) \/ ComputeEst(p) \/ BroadcastP2(p) \/ DecideMatched(p) \/ Choose(p) \/ Crash(p)
  \/ \E p \in Processes, m \in MsgSpace : ReceiveP1(p, m) \/ ReceiveP2(p, m)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in Processes, m \in MsgSpace : ReceiveP1(p, m))
  /\ WF_vars(\E p \in Processes, m \in MsgSpace : ReceiveP2(p, m))
  /\ WF_vars(\E p \in Processes : ComputeEst(p))
  /\ WF_vars(\E p \in Processes : DecideMatched(p))
  /\ WF_vars(\E p \in Processes : Choose(p))

Validity ==
  \A p \in Processes : decided[p] # Bottom => decided[p] \in {proposal[q] : q \in Processes}

Agreement ==
  \A p, q \in Processes : (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

====