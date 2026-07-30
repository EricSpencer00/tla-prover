---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME T >= F /\ 2 * T < N /\ N > 0 /\ Bottom \notin Values

MsgTypes == {"phase1", "phase2"}

VARIABLES loc, view, propose, est, decision, crashed, sent, recv

vars == <<loc, view, propose, est, decision, crashed, sent, recv>>

Msgs == [type: MsgTypes, val: Values, src: 1..N, est: Values \cup {Bottom}]

Init ==
  /\ loc = [n \in 1..N |-> "broadcast1"]
  /\ propose = [n \in 1..N |-> CHOOSE x \in Values : TRUE]
  /\ view = [n \in 1..N |-> [m \in 1..N |-> Bottom]]
  /\ est = [n \in 1..N |-> Bottom]
  /\ decision = [n \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [n \in 1..N |-> {}]

Sends(p, v) == Cardinality({m \in recv[p] : m.val = v})
Recs(p, v) == Cardinality({m \in recv[p] : m.type = "phase2" /\ m.est = v})

MaxVal(S) == IF S = {} THEN Bottom ELSE CHOOSE m \in S : \A k \in S : k <= m

\* Phase 1: broadcast proposal and collect.
Broadcast1(n) ==
  /\ loc[n] = "broadcast1"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> propose[n], src |-> n, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![n] = "waiting1"]
  /\ UNCHANGED <<view, propose, est, decision, crashed, recv>>

\* Receiving updates the local view only when the message matches the phase.
ReceivePhase1(n, m) ==
  /\ loc[n] = "waiting1"
  /\ m \in sent
  /\ m.type = "phase1"
  /\ m.src \notin {p.src : p \in recv[n]}
  /\ view' = [view EXCEPT ![n][m.src] = m.val]
  /\ recv' = [recv EXCEPT ![n] = @ \cup {m}]
  /\ UNCHANGED <<loc, propose, est, decision, crashed, sent>>

MoveToBroadcast2(n) ==
  /\ loc[n] = "waiting1"
  /\ Cardinality({m \in recv[n] : m.type = "phase1"}) >= N - T
  /\ est' = [est EXCEPT ![n] = MaxVal({view[n][k] : k \in 1..N})]
  /\ loc' = [loc EXCEPT ![n] = "broadcast2"]
  /\ UNCHANGED <<view, propose, decision, crashed, sent, recv>>

\* Phase 2: broadcast estimated value and make a decision.
Broadcast2(n) ==
  /\ loc[n] = "broadcast2"
  /\ sent' = sent \cup {[type |-> "phase2", val |-> propose[n], src |-> n, est |-> est[n]]}
  /\ loc' = [loc EXCEPT ![n] = "waiting2"]
  /\ UNCHANGED <<view, propose, est, decision, crashed, recv>>

DecideOnVoted(n, v) ==
  /\ loc[n] = "waiting2"
  /\ Recs(n, v) >= N - T
  /\ decision' = [decision EXCEPT ![n] = v]
  /\ loc' = [loc EXCEPT ![n] = "done"]
  /\ UNCHANGED <<view, propose, est, crashed, sent, recv>>

\* When no estimate reaches the quorum, the process chooses deterministically.
ChooseArbiter(n, v) ==
  /\ loc[n] = "waiting2"
  /\ Cardinality({m \in recv[n] : m.type = "phase2"}) = N
  /\ v \in {view[n][k] : k \in 1..N}
  /\ decision' = [decision EXCEPT ![n] = v]
  /\ loc' = [loc EXCEPT ![n] = "done"]
  /\ UNCHANGED <<view, propose, est, crashed, sent, recv>>

Crash(n) ==
  /\ crashed < F
  /\ loc[n] \notin {"done", "crashed"}
  /\ crashed' = crashed + 1
  /\ loc' = [loc EXCEPT ![n] = "crashed"]
  /\ UNCHANGED <<view, propose, est, decision, sent, recv>>

Next ==
  \/ \E n \in 1..N: Broadcast1(n)
  \/ \E n \in 1..N, m \in sent: ReceivePhase1(n, m)
  \/ \E n \in 1..N: MoveToBroadcast2(n)
  \/ \E n \in 1..N: Broadcast2(n)
  \/ \E n \in 1..N, v \in Values: DecideOnVoted(n, v)
  \/ \E n \in 1..N, v \in Values: ChooseArbiter(n, v)
  \/ \E n \in 1..N: Crash(n)

Spec == Init /\ [][Next]_vars
        /\ UNCHANGED <<sent>>

TypeOK ==
  /\ loc \in [1..N -> {"broadcast1", "waiting1", "broadcast2",
                        "waiting2", "done", "crashed", "choosing"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ propose \in [1..N -> Values]
  /\ est \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..N
  /\ sent \subseteq Msgs
  /\ recv \in [1..N -> SUBSET Msgs]

Validity == \A n \in 1..N: decision[n] # Bottom => decision[n] \in Values

Agreement == \A m, n \in 1..N: (decision[m] # Bottom /\ decision[n] # Bottom)
                          => decision[m] = decision[n]

Termination == <>(\A n \in 1..N: loc[n] \in {"done", "crashed"})

\* C1: enough processes propose the maximum value.
AtLeastFplus1ProposeMax ==
  \E v \in Values: \A n \in 1..N: decision[n] = v
                   => Sends(n, v) >= F + 1

====