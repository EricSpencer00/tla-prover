---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Phase values a process may be in.
Locs == {"bcastphase1", "waitphase1", "prepare", "bcastphase2", "waitphase2",
         "choose", "done", "crashed"}

\* Message types.
Kinds == {"phase1", "phase2"}

VARIABLES loc, view, propose, estimate, decision, crashed, msgs, recvd

vars == <<loc, view, propose, estimate, decision, crashed, msgs, recvd>>

\* The maximum of a finite set; Bottom only when the set is empty.
MaxOf(S) == IF S = {} THEN Bottom ELSE CHOOSE x \in S : \A y \in S : y <= x

TypeOK ==
  /\ loc \in [1..N -> Locs]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ propose \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \subseteq (1..N)
  /\ msgs \subseteq [kind: Kinds, val: Values, est: Values \cup {Bottom},
                     sender: 1..N]
  /\ recvd \in [1..N -> SUBSET (1..N)]

Init ==
  /\ loc = [p \in 1..N |-> "bcastphase1"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ propose \in [1..N -> Values]
  /\ estimate = [p \in 1..N |-> Bottom]
  /\ decision = [p \in 1..N |-> Bottom]
  /\ crashed = {}
  /\ msgs = {}
  /\ recvd = [p \in 1..N |-> {}]

\* Phase 1 broadcast: a process sends its proposed value.
BroadcastPhase1(p) ==
  /\ loc[p] = "bcastphase1"
  /\ \A m \in msgs : ~(m.kind = "phase1" /\ m.sender = p)
  /\ msgs' = msgs \cup
       {[kind |-> "phase1", val |-> propose[p], est |-> Bottom, sender |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "waitphase1"]
  /\ UNCHANGED <<view, propose, estimate, decision, crashed, recvd>>

\* Phase 1 reception: update the local view for a matching kind message.
RecvPhase1(p, q) ==
  /\ loc[p] \in {"waitphase1", "prepare"}
  /\ q \notin recvd[p]
  /\ \E m \in msgs :
       /\ m.kind = "phase1"
       /\ m.sender = q
       /\ view' = [view EXCEPT ![p][q] = m.val]
  /\ recvd' = [recvd EXCEPT ![p] = recvd[p] \cup {q}]
  /\ UNCHANGED <<loc, propose, estimate, decision, crashed, msgs>>

\* A process that has collected enough distinct phase-1 values computes its estimate.
Prepare(p) ==
  /\ loc[p] \in {"waitphase1", "prepare"}
  /\ Cardinality(recvd[p]) >= N - T
  /\ estimate[p] = Bottom
  /\ estimate' = [estimate EXCEPT ![p] = MaxOf({view[p][q] : q \in recvd[p]})]
  /\ loc' = [loc EXCEPT ![p] = "bcastphase2"]
  /\ UNCHANGED <<view, propose, decision, crashed, msgs, recvd>>

\* Phase 2 broadcast: a process sends both its proposed value and its estimate.
BroadcastPhase2(p) ==
  /\ loc[p] = "bcastphase2"
  /\ estimate[p] # Bottom
  /\ \A m \in msgs : ~(m.kind = "phase2" /\ m.sender = p)
  /\ msgs' = msgs \cup
       {[kind |-> "phase2", val |-> propose[p], est |-> estimate[p],
          sender |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "waitphase2"]
  /\ UNCHANGED <<view, propose, estimate, decision, crashed, recvd>>

\* Phase 2 reception: update the local view for a matching kind message.
RecvPhase2(p, q) ==
  /\ loc[p] \in {"waitphase2", "choose"}
  /\ q \notin recvd[p]
  /\ \E m \in msgs :
       /\ m.kind = "phase2"
       /\ m.sender = q
       /\ view' = [view EXCEPT ![p][q] = m.est]
  /\ recvd' = [recvd EXCEPT ![p] = recvd[p] \cup {q}]
  /\ UNCHANGED <<loc, propose, estimate, decision, crashed, msgs>>

\* A process decides once a strong majority agrees on an estimated value.
Decide(p) ==
  /\ loc[p] = "waitphase2"
  /\ \E v \in Values :
       Cardinality({q \in recvd[p] : view[p][q] = v}) >= N - T
  /\ decision' = [decision EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, propose, estimate, crashed, msgs, recvd>>

\* If phase 2 falls short of a majority, the process chooses deterministically.
Choose(p) ==
  /\ loc[p] = "waitphase2"
  /\ recvd[p] = 1..N
  /\ loc' = [loc EXCEPT ![p] = "choose"]
  /\ UNCHANGED <<view, propose, estimate, decision, crashed, msgs, recvd>>

DeterministicChoose(p) ==
  /\ loc[p] = "choose"
  /\ \E v \in Values :
       /\ \E q \in 1..N : view[p][q] = v
       /\ decision' = [decision EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, propose, estimate, crashed, msgs, recvd>>

\* A process crashes, halting its participation (subject to the fault bound).
Crash(p) ==
  /\ p \notin crashed
  /\ Cardinality(crashed) < F
  /\ crashed' = crashed \cup {p}
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ UNCHANGED <<view, propose, estimate, decision, msgs, recvd>>

Next ==
  \/ \E p \in 1..N : BroadcastPhase1(p) \/ Prepare(p) \/ BroadcastPhase2(p)
                     \/ Decide(p) \/ Choose(p) \/ DeterministicChoose(p) \/ Crash(p)
  \/ \E p \in 1..N, q \in 1..N :
        RecvPhase1(p, q) \/ RecvPhase2(p, q)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..N : BroadcastPhase1(p))
  /\ WF_vars(\E p \in 1..N : RecvPhase1(p, 1))
  /\ WF_vars(\E p \in 1..N : RecvPhase1(p, 2))
  /\ WF_vars(\E p \in 1..N : RecvPhase1(p, 3))
  /\ WF_vars(\E p \in 1..N : RecvPhase1(p, 4))
  /\ WF_vars(\E p \in 1..N : Prepare(p))
  /\ WF_vars(\E p \in 1..N : BroadcastPhase2(p))
  /\ WF_vars(\E p \in 1..N : RecvPhase2(p, 1))
  /\ WF_vars(\E p \in 1..N : RecvPhase2(p, 2))
  /\ WF_vars(\E p \in 1..N : RecvPhase2(p, 3))
  /\ WF_vars(\E p \in 1..N : RecvPhase2(p, 4))
  /\ WF_vars(\E p \in 1..N : Decide(p))
  /\ WF_vars(\E p \in 1..N : Choose(p))
  /\ WF_vars(\E p \in 1..N : DeterministicChoose(p))
  /\ WF_vars(\E p \in 1..N : Crash(p))

\* No decided value is ever outside the proposal set.
Validity == \A p \in 1..N : decision[p] # Bottom => decision[p] \in Values

\* No two processes ever decide different values.
Agreement == \A p, q \in 1..N :
               (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Termination == <>(\A p \in 1..N : loc[p] \in {"done", "crashed"})

\* Condition C1: the maximum is proposed by enough processes to guarantee termination.
ConditionalTermination == Cardinality({p \in 1..N : propose[p] = MaxOf(Values)}) >= F + 1 => Termination

====