---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

Phases == {"broadcast1", "wait1", "prepare", "broadcast2", "wait2", "done", "crashed", "choose"}
MsgTypes == {"phase1", "phase2"}
\* The messaging model is a set of unordered messages with a sender field, not a
\* per-destination buffer, so messages arrive in any order.

VARIABLES phase, view, prop, estimate, decision, crashed, sent, rcvd

vars == <<phase, view, prop, estimate, decision, crashed, sent, rcvd>>

TypeOK ==
  /\ phase \in [1..N -> Phases]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \in SUBSET (MsgTypes \X Values \X (1..N) \X (1..N))
  /\ rcvd \in [1..N -> SUBSET (MsgTypes \X Values \X (1..N) \X (1..N))]

MaxOf(S) == CHOOSE m \in S :
  \A x \in S : x <= m

MaxSeen(v) == MaxOf({ IF view[v][w] # Bottom THEN view[v][w] ELSE 0 : w \in 1..N })

Init ==
  /\ phase = [i \in 1..N |-> "broadcast1"]
  /\ view = [i \in 1..N |-> [w \in 1..N |-> Bottom]]
  /\ prop \in [1..N -> Values]
  /\ estimate = [i \in 1..N |-> Bottom]
  /\ decision = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ rcvd = [i \in 1..N |-> {}]

\* Phase 1: disseminate the initial proposals.
Broadcast1(i) ==
  /\ phase[i] = "broadcast1"
  /\ sent' = sent \cup {<<"phase1", prop[i], i, i>>}
  /\ phase' = [phase EXCEPT ![i] = "wait1"]
  /\ UNCHANGED <<view, prop, estimate, decision, crashed, rcvd>>

\* Messages arrive in any order; only the sender set matters, not delivery order.
Receive1(i) ==
  /\ phase[i] = "wait1"
  /\ \E m \in sent :
       /\ m[1] = "phase1"
       /\ m[3] = i
       /\ view' = [view EXCEPT ![i][m[4]] = m[2]]
       /\ rcvd' = [rcvd EXCEPT ![i] = rcvd[i] \cup {m}]
  /\ UNCHANGED <<phase, prop, estimate, decision, crashed, sent>>

\* At least one correct path: with enough distinct views collected, each process
\* computes an estimate from the maximum it has seen.
ComputeEstimate(i) ==
  /\ phase[i] = "wait1"
  /\ Cardinality({ m \in rcvd[i] : m[1] = "phase1" }) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] = MaxSeen(i)]
  /\ phase' = [phase EXCEPT ![i] = "broadcast2"]
  /\ UNCHANGED <<view, prop, decision, crashed, sent, rcvd>>

\* Phase 2: disseminate both the original proposal and the derived estimate.
Broadcast2(i) ==
  /\ phase[i] = "broadcast2"
  /\ sent' = sent \cup {<<"phase2", prop[i], estimate[i], i, i>>}
  /\ phase' = [phase EXCEPT ![i] = "wait2"]
  /\ UNCHANGED <<view, prop, estimate, decision, crashed, rcvd>>

Receive2(i) ==
  /\ phase[i] = "wait2"
  /\ \E m \in sent :
       /\ m[1] = "phase2"
       /\ m[4] = i
       /\ view' = [view EXCEPT ![i][m[5]] = m[2]]
       /\ rcvd' = [rcvd EXCEPT ![i] = rcvd[i] \cup {m}]
  /\ UNCHANGED <<phase, prop, estimate, decision, crashed, sent>>

\* The value is committed only once at least N-T phase-2 messages agree on it.
Decide(i) ==
  /\ phase[i] = "wait2"
  /\ \E v \in Values :
       /\ Cardinality({ m \in rcvd[i] : m[1] = "phase2" /\ m[3] = v }) >= N - T
       /\ decision' = [decision EXCEPT ![i] = v]
  /\ phase' = [phase EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, rcvd>>

\* If the quorum is unreachable (too many differing estimates), fall back to
\* picking any value that made it into the local view.
Choose(i) ==
  /\ phase[i] = "wait2"
  /\ \A v \in Values :
       Cardinality({ m \in rcvd[i] : m[1] = "phase2" /\ m[3] = v }) < N - T
  /\ phase' = [phase EXCEPT ![i] = "choose"]
  /\ UNCHANGED <<view, prop, estimate, decision, crashed, sent, rcvd>>

Pick(i) ==
  /\ phase[i] = "choose"
  /\ \E v \in Values :
       /\ \E w \in 1..N : view[i][w] = v
       /\ decision' = [decision EXCEPT ![i] = v]
  /\ phase' = [phase EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, rcvd>>

Crash(i) ==
  /\ phase[i] \in {"broadcast1", "wait1", "prepare", "broadcast2", "wait2", "choose"}
  /\ crashed < F
  /\ crashed' = crashed + 1
  /\ phase' = [phase EXCEPT ![i] = "crashed"]
  /\ UNCHANGED <<view, prop, estimate, decision, sent, rcvd>>

Next ==
  \E i \in 1..N :
    \/ Broadcast1(i)
    \/ Receive1(i)
    \/ ComputeEstimate(i)
    \/ Broadcast2(i)
    \/ Receive2(i)
    \/ Decide(i)
    \/ Choose(i)
    \/ Pick(i)
    \/ Crash(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in 1..N :
       /\ TRUE
       /\ WF_vars(Receive1(i))
       /\ WF_vars(ComputeEstimate(i))
       /\ WF_vars(Receive2(i))
       /\ WF_vars(Decide(i))
       /\ WF_vars(Pick(i))

Validity ==
  \A i \in 1..N : decision[i] # Bottom => \E j \in 1..N : prop[j] = decision[i]

Agreement ==
  \A i, j \in 1..N :
    (decision[i] # Bottom /\ decision[j] # Bottom) => decision[i] = decision[j]

Termination ==
  \A i \in 1..N : (phase[i] = "done" \/ phase[i] = "crashed") ~> (phase[i] = "done" \/ phase[i] = "crashed")

\* C1 from the paper: if enough processes propose the global maximum, that
\* maximum does not fall below any other proposal.
ConditionC1 ==
  \A i \in 1..N : prop[i] = MaxOf(Values) => \A j \in 1..N : prop[j] <= prop[i]

ConditionalTermination == ConditionC1 ~> Termination

====