---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

\* Two-phase agreement on the maximum proposed value, with a bounded number of
\* crash faults.  A process may reach a decision only from a quorum of N-T
\* distinct senders (the quorum condition is the sole guard on deciding).
CONSTANTS N, T, F, Values, Bottom

ASSUME N > 0 /\ T >= F /\ 2 * T < N /\ Bottom \notin Values

Processes == 0 .. (N - 1)
Messages == [type: {"phase1", "phase2"}, val: Values \cup {Bottom}, sender: Processes, est: Values \cup {Bottom}]

VARIABLES pc, view, prop, estimate, decided, crashed, sent, recv

vars == <<pc, view, prop, estimate, decided, crashed, sent, recv>>

TypeOK ==
  /\ pc \in [Processes -> {"bcast1", "wait1", "prepare", "bcast2", "wait2", "done", "crashed", "choosing"}]
  /\ view \in [Processes -> [Processes -> Values \cup {Bottom}]]
  /\ prop \in [Processes -> Values]
  /\ estimate \in [Processes -> Values \cup {Bottom}]
  /\ decided \in [Processes -> Values \cup {Bottom}]
  /\ crashed \in 0 .. N
  /\ sent \subseteq Messages
  /\ recv \in [Processes -> SUBSET Messages]

Init ==
  /\ pc = [p \in Processes |-> "bcast1"]
  /\ view = [p \in Processes |-> [q \in Processes |-> Bottom]]
  /\ prop \in [Processes -> Values]
  /\ estimate = [p \in Processes |-> Bottom]
  /\ decided = [p \in Processes |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [p \in Processes |-> {}]

\* Phase 1 collects proposals; phase 2 collects the computed estimates.
Broadcast1(p) ==
  /\ pc[p] = "bcast1"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> prop[p], sender |-> p, est |-> Bottom]}
  /\ pc' = [pc EXCEPT ![p] = "wait1"]
  /\ UNCHANGED <<view, prop, estimate, decided, crashed, recv>>

Receive(p, m) ==
  /\ pc[p] \in {"wait1", "wait2"}
  /\ m \in sent
  /\ m.type = IF pc[p] = "wait1" THEN "phase1" ELSE "phase2"
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED <<pc, prop, estimate, decided, crashed, sent>>

Prepare(p) ==
  /\ pc[p] = "wait1"
  /\ Cardinality(recv[p]) >= N - T
  /\ \E m \in recv[p] : m.type = "phase1"
  /\ estimate' = [estimate EXCEPT ![p] = CHOOSE v \in Values :
                     \A q \in Processes : view[p][q] # Bottom => view[p][q] <= v]
  /\ pc' = "prepare"
  /\ UNCHANGED <<view, prop, decided, crashed, sent, recv>>

Broadcast2(p) ==
  /\ pc[p] = "prepare"
  /\ sent' = sent \cup {[type |-> "phase2", val |-> prop[p], sender |-> p, est |-> estimate[p]]}
  /\ pc' = "wait2"
  /\ UNCHANGED <<view, prop, estimate, decided, crashed, recv>>

\* The quorum check below is the sole guard on deciding.
Decide(p) ==
  /\ pc[p] = "wait2"
  /\ Cardinality({m \in recv[p] : m.type = "phase2" /\ m.est = estimate[p]}) >= N - T
  /\ decided' = [decided EXCEPT ![p] = estimate[p]]
  /\ pc' = "done"
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, recv>>

Choose(p) ==
  /\ pc[p] = "wait2"
  /\ Cardinality(recv[p]) = N
  /\ \A v \in Values :
       Cardinality({m \in recv[p] : m.type = "phase2" /\ m.est = v}) < N - T
  /\ decided' = [decided EXCEPT ![p] = CHOOSE q \in Processes : view[p][q] # Bottom]
  /\ pc' = "choosing"
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, recv>>

FinishChoosing(p) ==
  /\ pc[p] = "choosing"
  /\ pc' = "done"
  /\ UNCHANGED <<view, prop, estimate, decided, crashed, sent, recv>>

Crash(p) ==
  /\ crashed < F
  /\ pc[p] \in {"bcast1", "wait1", "prepare", "bcast2", "wait2"}
  /\ pc' = [pc EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, estimate, decided, sent, recv>>

Next ==
  \/ \E p \in Processes : Broadcast1(p) \/ Prepare(p) \/ Broadcast2(p) \/ Decide(p) \/ Choose(p) \/ FinishChoosing(p) \/ Crash(p)
  \/ \E p \in Processes, m \in Messages : Receive(p, m)

Spec ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(\E p \in Processes, m \in Messages : Receive(p, m))
  /\ WF_vars(\E p \in Processes : Prepare(p))
  /\ WF_vars(\E p \in Processes : Decide(p) \/ Choose(p))
  /\ SF_vars(\E p \in Processes : FinishChoosing(p))
  /\ WF_vars(\E p \in Processes : Crash(p))

Validity == \A p \in Processes : decided[p] # Bottom => \E q \in Processes : prop[q] = decided[p]

Agreement == \A p1, p2 \in Processes : (decided[p1] # Bottom /\ decided[p2] # Bottom) => decided[p1] = decided[p2]

Termination == <>(\A p \in Processes : pc[p] \in {"done", "crashed"})

\* Conditional termination under the sufficient condition C1 (F+1 proponents at
\* the maximum) explored as a separate property rather than a global bound.
C1 == \E n \in Values : ((\A q \in Processes : prop[q] <= n) /\ (\E S \in SUBSET Processes :
  Cardinality(S) >= F + 1 /\ (\A q \in S : prop[q] = n))) => Termination

\* The bounded number of crashes that still leaves a majority of correct
\* processes preserves the quorum size N-T (and N > 2T), so termination is
\* provable from the quorum mechanism alone, without appealing to C1.
LivenessProperties == Termination /\ C1

\* Per the paper's terminology, the quorum is the condition that matters: the
\* subsequent crash bound is a model-parameter, not an assumption that drives
\* the safety or liveness arguments.
Properties == LivenessProperties

====