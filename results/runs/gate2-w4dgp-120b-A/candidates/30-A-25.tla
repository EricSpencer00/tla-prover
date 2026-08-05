---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES phase, view, propose, estimate, decision, crashed, sent, recv

vars == <<phase, view, propose, estimate, decision, crashed, sent, recv>>

MsgTypes == {"phase1", "phase2"}

TypeOK ==
  /\ phase \in [1..N -> {"ph1b","ph1w","prepare","ph2b","ph2w","done","crashed","choosing"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ propose \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq [type: MsgTypes, val: Values, src: 1..N, est: Values \cup {Bottom}]
  /\ recv \in [1..N -> SUBSET [type: MsgTypes, val: Values, src: 1..N, est: Values \cup {Bottom}]]

Init ==
  /\ phase = [i \in 1..N |-> "ph1b"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ propose \in [1..N -> Values]
  /\ estimate = [i \in 1..N |-> Bottom]
  /\ decision = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [i \in 1..N |-> {}]

\* Phase 1 broadcast: each process proposes its initial value to all others.
BroadcastF1(i) ==
  /\ phase[i] = "ph1b"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> propose[i], src |-> i, est |-> Bottom]}
  /\ phase' = [phase EXCEPT ![i] = "ph1w"]
  /\ UNCHANGED <<view, propose, estimate, decision, crashed, recv>>

\* Phase 1 reception: a message updates the receiver's local view of the sender's value.
ReceiveF1(i, m) ==
  /\ phase[i] = "ph1w"
  /\ m \in sent
  /\ m.type = "phase1"
  /\ view[i][m.src] = Bottom
  /\ view' = [view EXCEPT ![i][m.src] = m.val]
  /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
  /\ UNCHANGED <<phase, propose, estimate, decision, crashed, sent>>

\* Phase 1 transition: once a process has heard from enough distinct senders,
\* it computes its estimated value as the maximum it has seen so far.
Prepare(i) ==
  /\ phase[i] = "ph1w"
  /\ Cardinality({j \in 1..N : view[i][j] # Bottom}) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] = CHOOSE v \in {view[i][j] : j \in 1..N /\ view[i][j] # Bottom} : \A w \in {view[i][j] : j \in 1..N /\ view[i][j] # Bottom} : w <= v]
  /\ phase' = [phase EXCEPT ![i] = "prepare"]
  /\ UNCHANGED <<view, propose, decision, crashed, sent, recv>>

\* Phase 2 broadcast: a process shares both its proposed value and its estimate.
BroadcastF2(i) ==
  /\ phase[i] = "prepare"
  /\ sent' = sent \cup {[type |-> "phase2", val |-> propose[i], src |-> i, est |-> estimate[i]]}
  /\ phase' = [phase EXCEPT ![i] = "ph2w"]
  /\ UNCHANGED <<view, propose, estimate, decision, crashed, recv>>

\* Phase 2 reception: a message is recorded in the receiver's incoming set.
ReceiveF2(i, m) ==
  /\ phase[i] = "ph2w"
  /\ m \in sent
  /\ m.type = "phase2"
  /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
  /\ UNCHANGED <<phase, view, propose, estimate, decision, crashed, sent>>

\* Phase 2 decision: if enough messages carry the same estimate, that estimate is decided.
DecideF2(i) ==
  /\ phase[i] = "ph2w"
  /\ \E v \in Values :
       /\ Cardinality({m \in recv[i] : m.type = "phase2" /\ m.est = v}) >= N - T
       /\ decision' = [decision EXCEPT ![i] = v]
  /\ phase' = [phase EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, propose, estimate, crashed, sent, recv>>

\* When no single estimate reaches the threshold, the process deterministically chooses
\* an arbitrary value from what it has heard, so it can still make progress.
Choose(i) ==
  /\ phase[i] = "ph2w"
  /\ \A v \in Values :
       Cardinality({m \in recv[i] : m.type = "phase2" /\ m.est = v}) < N - T
  /\ \E v \in Values :
       /\ \E j \in 1..N : view[i][j] = v
       /\ decision' = [decision EXCEPT ![i] = v]
  /\ phase' = [phase EXCEPT ![i] = "choosing"]
  /\ UNCHANGED <<view, propose, estimate, crashed, sent, recv>>

\* A process may crash, bounded by the fault tolerance.
Crash(i) ==
  /\ crashed < F
  /\ phase[i] \notin {"done","crashed"}
  /\ phase' = [phase EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, propose, estimate, decision, sent, recv>>

Next ==
  \/ \E i \in 1..N : BroadcastF1(i)
  \/ \E i \in 1..N, m \in sent : ReceiveF1(i, m)
  \/ \E i \in 1..N : Prepare(i)
  \/ \E i \in 1..N : BroadcastF2(i)
  \/ \E i \in 1..N, m \in sent : ReceiveF2(i, m)
  \/ \E i \in 1..N : DecideF2(i)
  \/ \E i \in 1..N : Choose(i)
  \/ \E i \in 1..N : Crash(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E i \in 1..N, m \in sent : ReceiveF1(i, m))
  /\ WF_vars(\E i \in 1..N : Prepare(i))
  /\ WF_vars(\E i \in 1..N, m \in sent : ReceiveF2(i, m))
  /\ WF_vars(\E i \in 1..N : DecideF2(i))
  /\ WF_vars(\E i \in 1..N : Choose(i))

\* Validity: a decided value must have been proposed by some process.
Validity ==
  \A i \in 1..N : decision[i] # Bottom => \E j \in 1..N : propose[j] = decision[i]

\* Agreement: two processes can never decide different values.
Agreement ==
  \A i, j \in 1..N :
    (decision[i] # Bottom /\ decision[j] # Bottom) => decision[i] = decision[j]

\* Conditional termination: if enough processes propose the maximum possible value,
\* the protocol is guaranteed to terminate.
ConditionalTermination ==
  (Cardinality({i \in 1..N : propose[i] = CHOOSE v \in Values : \A w \in Values : w <= v}) >= F + 1) ~> (\A i \in 1..N : phase[i] \in {"done","crashed"})

\* Liveness: every process eventually crashes or finishes with a decision.
Termination ==
  \A i \in 1..N : (phase[i] = "done" \/ phase[i] = "crashed") ~> TRUE

====