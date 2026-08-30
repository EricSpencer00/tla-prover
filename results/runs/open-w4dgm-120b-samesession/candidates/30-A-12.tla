---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* A process is identified by a number 1..N; message fields are ordered for
\* deterministic reception, not to model any ordering guarantee.
Processes == 1..N
MessageTypes == {"phase1", "phase2"}
MaxV == CHOOSE v \in Values : \A w \in Values : w <= v

VARIABLES phase, view, propose, estimate, decided, crashed, sent, recv

vars == <<phase, view, propose, estimate, decided, crashed, sent, recv>>

Views == [Processes -> Values \cup {Bottom}]
DecidedStates == Values \cup {Bottom}

RECURSIVE MaxOf(_)
MaxOf(S) ==
    IF S = {} THEN Bottom
    ELSE LET x == CHOOSE y \in S : TRUE
         IN IF MaxV \in S THEN MaxV ELSE MaxOf(S \ {x})

Init ==
    /\ phase = [i \in Processes |-> "broadcast1"]
    /\ view = [i \in Processes |-> [j \in Processes |-> Bottom]]
    /\ propose \in [i \in Processes |-> Values]
    /\ estimate = [i \in Processes |-> Bottom]
    /\ decided = [i \in Processes |-> Bottom]
    /\ crashed = 0
    /\ sent = {}
    /\ recv = [i \in Processes |-> {}]

NextMessage(i, t, v, e) ==
    [sender |-> i, type |-> t, value |-> v, senderEst |-> e]

\* Phase 1: broadcast only the proposal; phase 2: broadcast both values.
Broadcast(i) ==
    /\ phase[i] = "broadcast1"
    /\ sent' = sent \cup {NextMessage(i, "phase1", propose[i], Bottom)}
    /\ phase' = [phase EXCEPT ![i] = "wait1"]
    /\ UNCHANGED <<view, propose, estimate, decided, crashed, recv>>

ReceivePhase1(i, m) ==
    /\ phase[i] = "wait1"
    /\ m \in sent
    /\ m.type = "phase1"
    /\ view[i][m.sender] = Bottom
    /\ view' = [view EXCEPT ![i][m.sender] = m.value]
    /\ recv' = [recv EXCEPT ![i] = @ \cup {m}]
    /\ UNCHANGED <<phase, propose, estimate, decided, crashed, sent>>

\* The always-enabled transition, guarded by the message count, is what keeps
\* a process from stalling forever when messages are slow rather than lost.
ComputeEstimate(i) ==
    /\ phase[i] = "wait1"
    /\ Cardinality({m \in recv[i] : m.type = "phase1"}) >= N - T
    /\ estimate' = [estimate EXCEPT ![i] = MaxOf({view[i][j] : j \in Processes})]
    /\ phase' = [phase EXCEPT ![i] = "broadcast2"]
    /\ UNCHANGED <<view, propose, decided, crashed, sent, recv>>

BroadcastPhase2(i) ==
    /\ phase[i] = "broadcast2"
    /\ sent' = sent \cup {NextMessage(i, "phase2", propose[i], estimate[i])}
    /\ phase' = [phase EXCEPT ![i] = "wait2"]
    /\ UNCHANGED <<view, propose, estimate, decided, crashed, recv>>

ReceivePhase2(i, m) ==
    /\ phase[i] = "wait2"
    /\ m \in sent
    /\ m.type = "phase2"
    /\ view[i][m.sender] = Bottom
    /\ view' = [view EXCEPT ![i][m.sender] = m.value]
    /\ recv' = [recv EXCEPT ![i] = @ \cup {m}]
    /\ UNCHANGED <<phase, propose, estimate, decided, crashed, sent>>

DecideByQuorum(i) ==
    /\ phase[i] = "wait2"
    /\ \E c \in DecidedStates :
         /\ Cardinality({m \in recv[i] : m.type = "phase2" /\ m.senderEst = c}) >= N - T
         /\ decided' = [decided EXCEPT ![i] = c]
    /\ phase' = [phase EXCEPT ![i] = "done"]
    /\ UNCHANGED <<view, propose, estimate, crashed, sent, recv>>

\* Deterministic fallback so no process is left waiting forever.
ChooseUnique(i) ==
    /\ phase[i] = "wait2"
    /\ \A c \in DecidedStates :
         Cardinality({m \in recv[i] : m.type = "phase2" /\ m.senderEst = c}) < N - T
    /\ \E v \in Values :
         /\ \E c \in {m.senderEst : m \in recv[i] : m.type = "phase2"} : v = c
         /\ decided' = [decided EXCEPT ![i] = v]
    /\ phase' = [phase EXCEPT ![i] = "choose"]
    /\ UNCHANGED <<view, propose, estimate, crashed, sent, recv>>

DecideByChoosing(i) ==
    /\ phase[i] = "choose"
    /\ phase' = [phase EXCEPT ![i] = "done"]
    /\ UNCHANGED <<view, propose, estimate, decided, crashed, sent, recv>>

Crash(i) ==
    /\ phase[i] \in {"broadcast1", "wait1", "broadcast2", "wait2"}
    /\ crashed < F
    /\ phase' = [phase EXCEPT ![i] = "crashed"]
    /\ crashed' = crashed + 1
    /\ UNCHANGED <<view, propose, estimate, decided, sent, recv>>

Next ==
    \/ \E i \in Processes : Broadcast(i)
    \/ \E i \in Processes, m \in sent : ReceivePhase1(i, m)
    \/ \E i \in Processes : ComputeEstimate(i)
    \/ \E i \in Processes : BroadcastPhase2(i)
    \/ \E i \in Processes, m \in sent : ReceivePhase2(i, m)
    \/ \E i \in Processes : DecideByQuorum(i)
    \/ \E i \in Processes : ChooseUnique(i)
    \/ \E i \in Processes : DecideByChoosing(i)
    \/ \E i \in Processes : Crash(i)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A i \in Processes, m \in sent : WF_vars(ReceivePhase1(i, m))
    /\ \A i \in Processes : WF_vars(ComputeEstimate(i))
    /\ \A i \in Processes, m \in sent : WF_vars(ReceivePhase2(i, m))
    /\ \A i \in Processes : SF_vars(DecideByQuorum(i))
    /\ \A i \in Processes : WF_vars(ChooseUnique(i))
    /\ \A i \in Processes : WF_vars(DecideByChoosing(i))
    /\ \A i \in Processes : WF_vars(Crash(i))

TypeOK ==
    /\ phase \in [Processes -> {"broadcast1", "wait1", "broadcast2", "wait2", "done", "crashed", "choose"}]
    /\ view \in [Processes -> Views]
    /\ propose \in [Processes -> Values]
    /\ estimate \in [Processes -> Values \cup {Bottom}]
    /\ decided \in [Processes -> DecidedStates]
    /\ crashed \in 0..F
    /\ sent \subseteq [sender : Processes, type : MessageTypes, value : Values, senderEst : Values \cup {Bottom}]
    /\ recv \in [Processes -> SUBSET [sender : Processes, type : MessageTypes, value : Values, senderEst : Values \cup {Bottom}]]

Validity ==
    \A i \in Processes : decided[i] # Bottom => \E j \in Processes : propose[j] = decided[i]

Agreement ==
    \A i, j \in Processes : (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

Termination ==
    \A i \in Processes : (phase[i] \in {"broadcast1", "wait1", "broadcast2", "wait2"}) ~> (phase[i] \in {"done", "crashed"})

\* Condition C1: if the majority (F+1 of N) proposes the maximum value, every
\* process's estimate converges to it and the quorum decides it.
ConditionalTermination ==
    (\A i \in Processes : propose[i] = MaxV) ~> (\A i \in Processes : decided[i] = MaxV)

====