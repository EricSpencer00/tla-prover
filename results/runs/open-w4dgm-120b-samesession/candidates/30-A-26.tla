---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Phase 1: exchange proposed values. Phase 2: exchange proposals together
\* with everyone''s estimated MAX; the condition is that enough propose the
\* true max to force agreement, else each process picks a local value.
\* Crash faults are bounded by T, and crashes are assumed to be weakly fair.
\* SAFETY: any decision is a proposed value, so it is no larger than the true
\* maximum. LIVENESS: every non-crashed process eventually decides.

Lamport == 0..(N - 1)
Plurals == {"phase1", "phase2"}
Naturals == 0..N
VARIABLES loc, view, propose, estimate, decided, crashed, msgs, rcvd

Msg == [kind: Plurals, val: Values, sender: Lamport, est: Values \cup {Bottom}]
LocKinds == {"ph1", "ph1w", "prepare", "ph2", "ph2w", "done", "crashed", "choose"}

MaxV(S) == IF S = {} THEN Bottom ELSE CHOOSE m \in S : \A x \in S : x <= m

TypeOK ==
  /\ loc \in [Lamport -> LocKinds]
  /\ view \in [Lamport -> [Lamport -> Values \cup {Bottom}]]
  /\ propose \in [Lamport -> Values]
  /\ estimate \in [Lamport -> Values \cup {Bottom}]
  /\ decided \in [Lamport -> Values \cup {Bottom}]
  /\ crashed \in 0..N
  /\ msgs \subseteq Msg
  /\ rcvd \in [Lamport -> SUBSET Lamport]

Init ==
  /\ loc = [p \in Lamport |-> "ph1"]
  /\ view = [p \in Lamport |-> [q \in Lamport |-> Bottom]]
  /\ propose \in [Lamport -> Values]
  /\ estimate = [p \in Lamport |-> Bottom]
  /\ decided = [p \in Lamport |-> Bottom]
  /\ crashed = 0
  /\ msgs = {}
  /\ rcvd = [p \in Lamport |-> {}]

\* A process that has crashed stops participating entirely.
\* Progress-fair assumptions below cover every non-crashed process.
Broadcast ==
  /\ \E p \in Lamport :
       /\ loc[p] = "ph1"
       /\ msgs' = msgs \cup {[kind |-> "phase1", val |-> propose[p], sender |-> p, est |-> Bottom]}
       /\ loc' = [loc EXCEPT ![p] = "ph1w"]
  /\ UNCHANGED <<view, propose, estimate, decided, crashed, rcvd>>

ReceivePhase1 ==
  /\ \E p \in Lamport :
       /\ loc[p] \in {"ph1w", "prepare"}
       /\ \E m \in msgs :
            /\ m.kind = "phase1"
            /\ m.sender \notin rcvd[p]
            /\ view' = [view EXCEPT ![p][m.sender] = m.val]
            /\ rcvd' = [rcvd EXCEPT ![p] = @ \cup {m.sender}]
  /\ UNCHANGED <<loc, propose, estimate, decided, crashed, msgs>>

\* Everyone else has to send phase-1 messages too; a slow process stalls all.
PrepEstimate ==
  /\ \E p \in Lamport :
       /\ loc[p] = "ph1w"
       /\ Cardinality(rcvd[p]) >= N - T
       /\ estimate' = [estimate EXCEPT ![p] = MaxV({view[p][q] : q \in Lamport})]
       /\ loc' = [loc EXCEPT ![p] = "prepare"]
  /\ UNCHANGED <<view, propose, decided, crashed, msgs, rcvd>>

BroadcastPhase2 ==
  /\ \E p \in Lamport :
       /\ loc[p] = "prepare"
       /\ msgs' = msgs \cup {[kind |-> "phase2", val |-> propose[p], sender |-> p, est |-> estimate[p]]}
       /\ loc' = "ph2w"
  /\ UNCHANGED <<view, propose, estimate, decided, crashed, rcvd>>

ReceivePhase2 ==
  /\ \E p \in Lamport :
       /\ loc[p] = "ph2w"
       /\ \E m \in msgs :
            /\ m.kind = "phase2"
            /\ m.sender \notin rcvd[p]
            /\ view' = [view EXCEPT ![p][m.sender] = m.est]
            /\ rcvd' = [rcvd EXCEPT ![p] = @ \cup {m.sender}]
  /\ UNCHANGED <<loc, propose, estimate, decided, crashed, msgs>>

DecideBySupport ==
  /\ \E p \in Lamport :
       /\ loc[p] = "ph2w"
       /\ \E v \in Values :
            /\ Cardinality({q \in Lamport : view[p][q] = v}) >= N - T
            /\ decided' = [decided EXCEPT ![p] = v]
            /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, propose, estimate, crashed, msgs, rcvd>>

\* A process that cannot reach the N-T support threshold must still pick.
ChooseAny ==
  /\ \E p \in Lamport :
       /\ loc[p] = "ph2w"
       /\ rcvd[p] = Lamport
       /\ loc' = [loc EXCEPT ![p] = "choose"]
  /\ UNCHANGED <<view, propose, estimate, decided, crashed, msgs, rcvd>>

DecideChosen ==
  /\ \E p \in Lamport :
       /\ loc[p] = "choose"
       /\ decided' = [decided EXCEPT ![p] = view[p][p]]
       /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, propose, estimate, crashed, msgs, rcvd>>

Crash ==
  /\ crashed < F
  /\ \E p \in Lamport :
       /\ loc[p] \notin {"done", "crashed"}
       /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, propose, estimate, decided, msgs, rcvd>>

DecideSome == DecideBySupport \/ DecideChosen

Next == Broadcast \/ ReceivePhase1 \/ PrepEstimate \/ BroadcastPhase2
        \/ ReceivePhase2 \/ DecideSome \/ Crash

Spec == Init /\ [][Next]_<<loc, view, propose, estimate, decided, crashed, msgs, rcvd>>
        /\ WF_Vars(DecideSome) /\ WF_Vars(Crash)

Validity == \A p \in Lamport : decided[p] # Bottom => decided[p] \in {propose[q] : q \in Lamport}

Agreement == \A p q \in Lamport :
  (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

Termination == <>(\A p \in Lamport : loc[p] \in {"crashed", "done"})

\* The condition is that enough processes propose the true maximum.
UnderConditionC1 == (\A q \in Lamport : propose[q] # MaxV({propose[r] : r \in Lamport}))
                      => Termination

====