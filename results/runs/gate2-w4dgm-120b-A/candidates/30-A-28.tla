---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom
ASSUME Bottom \notin Values

Locations == {"broadcastPhase1", "waitPhase1", "prepare", "broadcastPhase2", "waitPhase2", "done", "crashed", "choosing"}
MsgKinds == {"phase1", "phase2"}
\* The message structure is a tuple; the third entry is the estimated value and is
\* only set for phase2 messages.
Msgs == (MsgKinds \X Values \X (0..N) \X (Values \cup {Bottom}))
\* A local view is a vector of values, so the whole matrix is a set of such vectors.
Views == [N -> Values \cup {Bottom}]

VARIABLES loc, view, propose, estimate, decided, crashed, sent, received

vars == <<loc, view, propose, estimate, decided, crashed, sent, received>>

TypeOK ==
  /\ loc \in [0..N-1 -> Locations]
  /\ view \in [0..N-1 -> Views]
  /\ propose \in [0..N-1 -> Values]
  /\ estimate \in [0..N-1 -> Values \cup {Bottom}]
  /\ decided \in [0..N-1 -> Values \cup {Bottom}]
  /\ crashed \in 0..N
  /\ sent \subseteq Msgs
  /\ received \subseteq Msgs

Init ==
  /\ loc = [p \in 0..N-1 |-> "broadcastPhase1"]
  /\ view = [p \in 0..N-1 |-> [q \in 0..N-1 |-> Bottom]]
  /\ propose \in [0..N-1 -> Values]
  /\ estimate = [p \in 0..N-1 |-> Bottom]
  /\ decided = [p \in 0..N-1 |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ received = {}

BroadcastPhase1(p) ==
  /\ loc[p] = "broadcastPhase1"
  /\ sent' = sent \cup {<<"phase1", propose[p], p, Bottom>>}
  /\ loc' = [loc EXCEPT ![p] = "waitPhase1"]
  /\ UNCHANGED <<view, propose, estimate, decided, crashed, received>>

\* A message is only assimilated when its phase matches the receiver's current phase.
ReceivePhase1(p, m) ==
  /\ loc[p] = "waitPhase1"
  /\ m \in received
  /\ m[1] = "phase1"
  /\ view' = [view EXCEPT ![p][m[3]] = m[2]]
  /\ UNCHANGED <<loc, propose, estimate, decided, crashed, sent, received>>

Prepare(p) ==
  /\ loc[p] = "waitPhase1"
  /\ Cardinality({q \in 0..N-1 : view[p][q] # Bottom}) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = Max({view[p][q] : q \in 0..N-1})]
  /\ loc' = [loc EXCEPT ![p] = "broadcastPhase2"]
  /\ UNCHANGED <<view, propose, decided, crashed, sent, received>>

BroadcastPhase2(p) ==
  /\ loc[p] = "broadcastPhase2"
  /\ sent' = sent \cup {<<"phase2", propose[p], p, estimate[p]>>}
  /\ loc' = [loc EXCEPT ![p] = "waitPhase2"]
  /\ UNCHANGED <<view, propose, estimate, decided, crashed, received>>

\* The phase-2 quorum condition counts how many phase-2 messages agree on the
\* same estimated value, which is what forces convergence.
ReceivePhase2(p, m) ==
  /\ loc[p] = "waitPhase2"
  /\ m \in received
  /\ m[1] = "phase2"
  /\ view' = [view EXCEPT ![p][m[3]] = m[4]]
  /\ UNCHANGED <<loc, propose, estimate, decided, crashed, sent, received>>

Decide(p) ==
  /\ loc[p] = "waitPhase2"
  /\ Cardinality({q \in 0..N-1 : view[p][q] = estimate[p]}) >= N - T
  /\ decided' = [decided EXCEPT ![p] = estimate[p]]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, propose, estimate, crashed, sent, received>>

Choose(p) ==
  /\ loc[p] = "waitPhase2"
  /\ {q \in 0..N-1 : view[p][q] # Bottom} = 0..N-1
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, propose, estimate, decided, crashed, sent, received>>

MakeChoice(p) ==
  /\ loc[p] = "choosing"
  /\ \E v \in Values : v \in {view[p][q] : q \in 0..N-1} /\ decided' = [decided EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, propose, estimate, crashed, sent, received>>

Crash(p) ==
  /\ crashed < F
  /\ loc[p] \notin {"crashed", "done"}
  /\ crashed' = crashed + 1
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ UNCHANGED <<view, propose, estimate, decided, sent, received>>

ReceiveAny(p, m) == ReceivePhase1(p, m) \/ ReceivePhase2(p, m)

Next ==
  \/ \E p \in 0..N-1 : BroadcastPhase1(p) \/ Prepare(p) \/ BroadcastPhase2(p) \/ Decide(p) \/ Choose(p) \/ MakeChoice(p) \/ Crash(p)
  \/ \E p \in 0..N-1, m \in Msgs : ReceiveAny(p, m)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in 0..N-1, m \in Msgs : WF_vars(ReceiveAny(p, m))

Validity == \A p \in 0..N-1 : decided[p] # Bottom => \E q \in 0..N-1 : propose[q] = decided[p]

Agreement == \A p1, p2 \in 0..N-1 : (decided[p1] # Bottom /\ decided[p2] # Bottom) => decided[p1] = decided[p2]

\* Decision on the maximum value propagates from the maximum proposer, so weak fairness
\* on the number of crash events is enough; the receiver side is already strongly fair.
Termination ==
  <>(\A p \in 0..N-1 : loc[p] \in {"crashed", "done"})

ConditionC1 ==
  \A m \in Values : (\A q \in 0..N-1 : propose[q] = m) => m = Max(Values)

\* The guarantee holds only when the quorum threshold is available: the number of
\* faults the protocol tolerates is strictly less than half the processes.
SuccessUnderConditionC1 == ConditionC1 => Termination

\* The quorum bound is a strict majority of the current population, which is
\* insensitive to how many processes have actually taken their last step.
QuorumStillMajority == 2 * (N - crashed) > N

====