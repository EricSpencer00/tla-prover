---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

Message == [type: {"phase1", "phase2"}, val: Values, sender: 1..N, est: Values]

VARIABLES loc, view, proposal, estimate, decision, crashed, sent, received

vars == <<loc, view, proposal, estimate, decision, crashed, sent, received>>

TypeOK ==
  /\ loc \in [1..N -> {"phase1", "phase1_wait", "prepare", "phase2", "phase2_wait", "done", "crashed", "choose"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ proposal \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq Message
  /\ received \in [1..N -> SUBSET Message]

Init ==
  /\ loc = [i \in 1..N |-> "phase1"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ proposal \in [1..N -> Values]
  /\ estimate = [i \in 1..N |-> Bottom]
  /\ decision = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ received = [i \in 1..N |-> {}]

\* Each process broadcasts its proposal as a phase-1 message.
BroadcastPhase1(i) ==
  /\ loc[i] = "phase1"
  /\ \A m \in sent : ~(m.type = "phase1" /\ m.sender = i)
  /\ sent' = sent \cup {[type |-> "phase1", val |-> proposal[i], sender |-> i, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![i] = "phase1_wait"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, received>>

\* A process updates its local view upon receiving a phase-matched message.
Receive(i, m) ==
  /\ m \in sent
  /\ m.sender # i
  /\ m.type = IF loc[i] \in {"phase1_wait", "prepare"} THEN "phase1"
              ELSE IF loc[i] \in {"phase2_wait", "choose"} THEN "phase2"
              ELSE "none"
  /\ m \notin received[i]
  /\ view' = [view EXCEPT ![i][m.sender] = m.val]
  /\ received' = [received EXCEPT ![i] = @ \cup {m}]
  /\ UNCHANGED <<loc, proposal, estimate, decision, crashed, sent>>

\* After collecting a quorum of phase-1 messages, compute the maximum.
Prepare(i) ==
  /\ loc[i] = "phase1_wait"
  /\ Cardinality({m \in received[i] : m.type = "phase1"}) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] = CHOOSE x \in Values : \A j \in 1..N :
                     (view[i][j] # Bottom) => (view[i][j] <= x)]
  /\ loc' = [loc EXCEPT ![i] = "prepare"]
  /\ UNCHANGED <<view, proposal, decision, crashed, sent, received>>

\* Each process broadcasts a phase-2 message with its proposal and estimate.
BroadcastPhase2(i) ==
  /\ loc[i] = "prepare"
  /\ \A m \in sent : ~(m.type = "phase2" /\ m.sender = i)
  /\ sent' = sent \cup {[type |-> "phase2", val |-> proposal[i], sender |-> i, est |-> estimate[i]]}
  /\ loc' = [loc EXCEPT ![i] = "phase2_wait"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, received>>

\* A unanimous high estimate among a quorum makes a decision.
DecideHigh(i) ==
  /\ loc[i] = "phase2_wait"
  /\ \E k \in Values :
       /\ Cardinality({m \in received[i] : m.type = "phase2" /\ m.est = k}) >= N - T
       /\ decision' = [decision EXCEPT ![i] = k]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposal, estimate, crashed, sent, received>>

\* If quorum agreement is impossible, the process deterministically chooses.
Choose(i) ==
  /\ loc[i] = "phase2_wait"
  /\ \A m \in sent : m.type = "phase2" => m.sender = i \/ m \in received[i]
  /\ loc' = [loc EXCEPT ![i] = "choose"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, sent, received>>

DecideChosen(i) ==
  /\ loc[i] = "choose"
  /\ \E k \in Values :
       /\ \A j \in 1..N : view[i][j] # Bottom => view[i][j] <= k
       /\ decision' = [decision EXCEPT ![i] = k]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposal, estimate, crashed, sent, received>>

Crash(i) ==
  /\ crashed < F
  /\ loc[i] # "crashed"
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, proposal, estimate, decision, sent, received>>

Next ==
  \/ \E i \in 1..N :
       BroadcastPhase1(i) \/ Prepare(i) \/ BroadcastPhase2(i) \/ DecideHigh(i) \/ Choose(i) \/ DecideChosen(i) \/ Crash(i)
  \/ \E i \in 1..N, m \in Message : Receive(i, m)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E i \in 1..N, m \in Message : Receive(i, m))
        /\ WF_vars(\E i \in 1..N : Prepare(i))
        /\ WF_vars(\E i \in 1..N : DecideHigh(i))
        /\ WF_vars(\E i \in 1..N : Choose(i))
        /\ WF_vars(\E i \in 1..N : BroadcastPhase2(i))

Validity == \A i \in 1..N : decision[i] # Bottom => \E j \in 1..N : proposal[j] = decision[i]

Agreement == \A i \in 1..N : decision[i] # Bottom => decision[i] = estimate[i]

Termination == \A i \in 1..N : loc[i] \in {"crashed", "done"}

C1 == \E S \subseteq Values :
        /\ \E f \in [S -> (1..N)] : Cardinality(S) = F + 1 /\ \A k \in S : proposal[f[k]] = CHOOSE x \in Values : \A y \in Values : y <= x
        /\ \A j \in 1..N : proposal[j] <= CHOOSE x \in S : TRUE

C1Termination == (C1 => Termination)
====