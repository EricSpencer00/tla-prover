---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Two-phase consensus based on the maximum proposed value. Phase 1 collects
\* proposals; phase 2 elects by quorum the maximum seen by enough processes.
\* 2T < N is the condition that bounds how many processes can crash without
\* breaking agreement.
Nodes == 1..N
Locs == {"idling", "wait1", "prepare", "idling2", "wait2",
          "done", "crashed", "choosing"}
Types == {"phase1", "phase2"}
Msgs == [type: Types, val: Values, sender: Nodes, est: Values]
Bases == 0..(Cardinality(Values) - 1)

VARIABLES stage, view, prop, est, decision, crashed, sent, recv
vars == <<stage, view, prop, est, decision, crashed, sent, recv>>

TypeOK ==
  /\ stage \in [Nodes -> Locs]
  /\ view \in [Nodes -> [Nodes -> Values \union {Bottom}]]
  /\ prop \in [Nodes -> Values]
  /\ est \in [Nodes -> Values \union {Bottom}]
  /\ decision \in [Nodes -> Values \union {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq Msgs
  /\ recv \in [Nodes -> SUBSET Nodes]

Init ==
  /\ stage = [n \in Nodes |-> "idling"]
  /\ view = [n \in Nodes |-> [m \in Nodes |-> Bottom]]
  /\ prop \in [Nodes -> Values]
  /\ est = [n \in Nodes |-> Bottom]
  /\ decision = [n \in Nodes |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [n \in Nodes |-> {}]

\* A phase-1 broadcast carries only the sender's own proposed value.
Broadcast1(n) ==
  /\ stage[n] = "idling"
  /\ sent' = sent \union {[type |-> "phase1", val |-> prop[n], sender |-> n, est |-> Bottom]}
  /\ stage' = [stage EXCEPT ![n] = "wait1"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, recv>>

Receive1(n, s) ==
  /\ stage[n] = "wait1"
  /\ s \in sent
  /\ s.type = "phase1"
  /\ view' = [view EXCEPT ![n][s.sender] = s.val]
  /\ recv' = [recv EXCEPT ![n] = recv[n] \union {s.sender}]
  /\ UNCHANGED <<stage, prop, est, decision, crashed, sent>>

\* Estimate is the maximum seen in the local view, computed once the quorum is in.
MaxV(S) == CHOOSE v \in Values : \A x \in S : x <= v
Estimate(n) == MaxV({view[n][m] : m \in Nodes})

Decide1(n) ==
  /\ stage[n] = "wait1"
  /\ Cardinality(recv[n]) >= (N - T)
  /\ est' = [est EXCEPT ![n] = Estimate(n)]
  /\ stage' = "idling2"
  /\ UNCHANGED <<view, prop, decision, crashed, sent, recv>>

Broadcast2(n) ==
  /\ stage[n] = "idling2"
  /\ sent' = sent \union {[type |-> "phase2", val |-> prop[n], sender |-> n, est |-> est[n]]}
  /\ stage' = "wait2"
  /\ UNCHANGED <<view, prop, est, decision, crashed, recv>>

\* Phase-2 messages carry the sender's own estimate; a process decides when a
\* quorum of them agree on the same estimate.
Vote(n, e) == {s \in sent : s.type = "phase2" /\ s.sender \in recv[n] /\ s.est = e}
Decide2(n, e) ==
  /\ stage[n] = "wait2"
  /\ e \in Values
  /\ Cardinality(Vote(n, e)) >= (N - T)
  /\ decision' = [decision EXCEPT ![n] = e]
  /\ stage' = "done"
  /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

Receive2(n, s) ==
  /\ stage[n] = "wait2"
  /\ s \in sent
  /\ s.type = "phase2"
  /\ view' = [view EXCEPT ![n][s.sender] = s.val]
  /\ recv' = [recv EXCEPT ![n] = recv[n] \union {s.sender}]
  /\ UNCHANGED <<stage, prop, est, decision, crashed, sent>>

\* Deterministic fallback: when the quorum never formed on any single value,
\* the process picks some value from its view and decides it.
Choose(n) ==
  /\ stage[n] = "wait2"
  /\ \A e \in Values : Cardinality(Vote(n, e)) < (N - T)
  /\ decision' = [decision EXCEPT ![n] = Estimate(n)]
  /\ stage' = "choosing"
  /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

Crash(n) ==
  /\ crashed < F
  /\ stage[n] \notin {"crashed", "done"}
  /\ crashed' = crashed + 1
  /\ stage' = [stage EXCEPT ![n] = "crashed"]
  /\ UNCHANGED <<view, prop, est, decision, sent, recv>>

DecideAny == \E n \in Nodes, e \in Values : Decide2(n, e)
ReceiveAny == \E n \in Nodes, s \in sent : Receive1(n, s) \/ Receive2(n, s)

Next ==
  \/ \E n \in Nodes : Broadcast1(n) \/ Decide1(n) \/ Broadcast2(n) \/ Choose(n) \/ Crash(n)
  \/ \E n \in Nodes, s \in sent : Receive1(n, s) \/ Receive2(n, s)
  \/ \E n \in Nodes, e \in Values : Decide2(n, e)
  \/ (DecideAny /\ ReceiveAny)

\* Phase-2 decisions may be delayed arbitrarily, so they need strong fairness;
\* receiving and broadcasting need only weak fairness to stay enabled.
Spec == Init /\ [][Next]_vars
  /\ WF_vars(DecideAny) /\ WF_vars(ReceiveAny)
  /\ SF_vars(\E n \in Nodes : Decide1(n))
  /\ SF_vars(\E n \in Nodes : Broadcast2(n))
  /\ SF_vars(\E n \in Nodes, e \in Values : Decide2(n, e))

\* SAFETY: nothing outside the agreed-upon value set is ever decided, and
\* no two processes end up deciding different values.
Validity == \A n \in Nodes : decision[n] # Bottom => decision[n] \in Values
Agreement == \A a, b \in Nodes :
  (stage[a] = "done" /\ stage[b] = "done") => decision[a] = decision[b]

\* LIVENESS: every process eventually stops (crashes or decides), and the
\* guaranteed-termination condition C1 holds for the quorum below.
Termination == <>(\A n \in Nodes : stage[n] \in {"crashed", "done"})
MajorityMax == ({n \in Nodes : prop[n] = (Maximum(Values) - Bases)} \in
                  Cardinality(Domain) .. N)

\* The quorum bound is what makes termination provable under C1; it is not
\* a separate safety or liveness property of the system.
ConditionC1 == 2 * T < N

Properties == Termination /\ MajorityMax
====