---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Phase-1 and phase-2 messages are distinguished by their type; phase-2
\* messages additionally carry the sender's estimated value.
Message == [type: {"phase1", "phase2"}, val: Values, sender: 1..N, est: Values \cup {Bottom}]

VARIABLES loc, view, prop, est, decision, crashed, sent, recv

vars == <<loc, view, prop, est, decision, crashed, sent, recv>>

TypeOK ==
  /\ loc \in [1..N -> {"broadcast1", "wait1", "prepare", "broadcast2", "wait2", "done", "crashed", "choosing"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ est \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq Message
  /\ recv \in [1..N -> SUBSET Message]

Init ==
  /\ loc = [p \in 1..N |-> "broadcast1"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ prop \in [1..N -> Values]
  /\ est = [p \in 1..N |-> Bottom]
  /\ decision = [p \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [p \in 1..N |-> {}]

Broadcast1(p) ==
  /\ loc[p] = "broadcast1"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> prop[p], sender |-> p, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![p] = "wait1"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, recv>>

\* A message is accepted only if its type matches the receiver's current phase.
Receive(p, m) ==
  /\ loc[p] \in {"wait1", "wait2"}
  /\ m \in sent
  /\ m.type = (IF loc[p] = "wait1" THEN "phase1" ELSE "phase2")
  /\ m.sender \notin {x.msg.sender : x \in recv[p]}
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED <<loc, prop, est, decision, crashed, sent>>

\* The estimate is the maximum of the receiver's local view.
ComputeEst(p) ==
  /\ loc[p] = "wait1"
  /\ Cardinality({x.msg.sender : x \in recv[p]}) >= N - T
  /\ est' = [est EXCEPT ![p] = CHOOSE v \in Values : \A q \in 1..N : view[p][q] # Bottom => q <= v]
  /\ loc' = [loc EXCEPT ![p] = "broadcast2"]
  /\ UNCHANGED <<view, prop, decision, crashed, sent, recv>>

Broadcast2(p) ==
  /\ loc[p] = "broadcast2"
  /\ sent' = sent \cup {[type |-> "phase2", val |-> prop[p], sender |-> p, est |-> est[p]]}
  /\ loc' = [loc EXCEPT ![p] = "wait2"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, recv>>

Decide(p) ==
  /\ loc[p] = "wait2"
  /\ Cardinality({x.msg.sender : x \in recv[p] : x.msg.est = est[p]}) >= N - T
  /\ decision' = [decision EXCEPT ![p] = est[p]]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

\* When no single estimate reaches the threshold, the process picks a value
\* it has actually observed in its local view.
Choose(p) ==
  /\ loc[p] = "wait2"
  /\ \A v \in Values : Cardinality({x.msg.sender : x \in recv[p] : x.msg.est = v}) < N - T
  /\ \E v \in Values : \A q \in 1..N : view[p][q] # Bottom => q <= v
  /\ decision' = [decision EXCEPT ![p] = CHOOSE v \in Values : \A q \in 1..N : view[p][q] # Bottom => q <= v]
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

Crash(p) ==
  /\ loc[p] \notin {"crashed", "done"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, est, decision, sent, recv>>

Next ==
  \/ \E p \in 1..N : Broadcast1(p)
  \/ \E p \in 1..N, m \in Message : Receive(p, m)
  \/ \E p \in 1..N : ComputeEst(p)
  \/ \E p \in 1..N : Broadcast2(p)
  \/ \E p \in 1..N : Decide(p)
  \/ \E p \in 1..N : Choose(p)
  \/ \E p \in 1..N : Crash(p)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..N, m \in Message : Receive(p, m))
  /\ WF_vars(\E p \in 1..N : ComputeEst(p))
  /\ WF_vars(\E p \in 1..N : Decide(p))
  /\ WF_vars(\E p \in 1..N : Choose(p))

Validity == \A p \in 1..N : decision[p] # Bottom => decision[p] \in {prop[q] : q \in 1..N}

Agreement == \A p, q \in 1..N : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Termination == <>(\A p \in 1..N : loc[p] \in {"done", "crashed"})

\* Condition C1: enough processes propose the global maximum to guarantee
\* termination (the condition from the paper's Figure 1).
C1 == \E S \in SUBSET (1..N) : Cardinality(S) >= F + 1 /\ \A p \in S : prop[p] = CHOOSE v \in Values : \A q \in 1..N : q <= v

ConditionalTermination == C1 ~> Termination

====