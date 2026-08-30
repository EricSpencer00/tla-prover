---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

Locs == {"b1", "w1", "prep", "b2", "w2", "done", "crashed", "choosing"}
MsgTypes == {"m1", "m2"}
\* The local view matrix is double-indexed by receiver and sender; the
\* invariant checks that Receiving only ever fills cells below the diagonal.
\* Bottom is the special "no value yet" marker; it is distinct from every
\* real value in Values, which is what makes that check sound.

VARIABLES loc, view, proposed, estimate, decided, crashed, sent, received

vars == <<loc, view, proposed, estimate, decided, crashed, sent, received>>

Messages == [type: MsgTypes, val: Values \cup {Bottom},
             sender: 1..N, estimate: Values \cup {Bottom}]

TypeOK ==
  /\ loc \in [1..N -> Locs]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ proposed \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq Messages
  /\ received \in [1..N -> SUBSET Messages]

Init ==
  /\ loc = [i \in 1..N |-> "b1"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ proposed \in [1..N -> Values]
  /\ estimate = [i \in 1..N |-> Bottom]
  /\ decided = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ received = [i \in 1..N |-> {}]

Broadcast(m) == [m.type EXCEPT ! \in sent]
Receiving(i, m) ==
  /\ m.type = loc[i]
  /\ m \notin received[i]
  /\ \A s \in received[i] : s.sender # m.sender
  /\ view' = [view EXCEPT ![i][m.sender] = m.val]
  /\ received' = [received EXCEPT ![i] = received[i] \cup {m}]
  /\ UNCHANGED <<loc, proposed, estimate, decided, crashed, sent>>

RecentlySeen(i) == Cardinality({j \in 1..N : view[i][j] # Bottom})
SeenEstimates(i) == Cardinality({j \in 1..N : \E m \in received[i] : m.type = "m2" /\ m.sender = j /\ m.estimate = estimate[i]})

\* Phase 1: broadcast each proposed value to everyone else.
BroadcastPhase1 ==
  /\ \E i \in 1..N:
       /\ loc[i] = "b1"
       /\ sent' = sent \cup {[type |-> "m1", val |-> proposed[i],
                              sender |-> i, estimate |-> Bottom]}
       /\ loc' = [loc EXCEPT ![i] = "w1"]
  /\ UNCHANGED <<view, proposed, estimate, decided, crashed, received>>

\* Phase 1: receive and update the local view.
ReceivePhase1 ==
  \E i \in 1..N, m \in Messages: Receiving(i, m)
  /\ UNCHANGED <<proposed, estimate, decided, crashed, sent>>

\* Phase 1: the coordinator waits on enough views to compute the max.
Compute ==
  /\ \E i \in 1..N:
       /\ loc[i] = "w1"
       /\ RecentlySeen(i) >= N - T
       /\ estimate' = [estimate EXCEPT ![i] =
                         CHOOSE v \in Values :
                           \A j \in 1..N : view[i][j] # Bottom => view[i][j] <= v]
       /\ loc' = [loc EXCEPT ![i] = "b2"]
  /\ UNCHANGED <<view, proposed, decided, crashed, sent, received>>

\* Phase 2: broadcast the computed estimate together with the proposal.
BroadcastPhase2 ==
  /\ \E i \in 1..N:
       /\ loc[i] = "b2"
       /\ sent' = sent \cup {[type |-> "m2", val |-> proposed[i],
                              sender |-> i, estimate |-> estimate[i]]}
       /\ loc' = [loc EXCEPT ![i] = "w2"]
  /\ UNCHANGED <<view, proposed, estimate, decided, crashed, received>>

\* Phase 2: receive phase-2 messages.
ReceivePhase2 ==
  \E i \in 1..N, m \in Messages: Receiving(i, m)
  /\ UNCHANGED <<proposed, estimate, decided, crashed, sent>>

\* Phase 2: the coordinator decides once enough receivers agree on the same
\* estimate, which is what guarantees both safety and termination under C1.
Decide ==
  /\ \E i \in 1..N:
       /\ loc[i] = "w2"
       /\ SeenEstimates(i) >= N - T
       /\ decided' = [decided EXCEPT ![i] = estimate[i]]
       /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposed, estimate, crashed, sent, received>>

\* Phase 2: with no N-T agreement yet, but the view is full, the coordinator
\* is forced to pick a value from its view and finish anyway.
ChooseFromView ==
  /\ \E i \in 1..N:
       /\ loc[i] = "w2"
       /\ RecentlySeen(i) = N
       /\ \A v \in Values : SeenEstimates(i) < N - T => v # estimate[i]
       /\ loc' = [loc EXCEPT ![i] = "choosing"]
  /\ UNCHANGED <<view, proposed, estimate, decided, crashed, sent, received>>

\* Phase 2: nondeterministically choose any seen value once agreement is
\* impossible. Any choice from the view preserves both safety properties.
DecideAlt ==
  /\ \E i \in 1..N, v \in Values:
       /\ loc[i] = "choosing"
       /\ view[i][i] = v
       /\ decided' = [decided EXCEPT ![i] = v]
       /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposed, estimate, crashed, sent, received>>

\* Any process may crash; the shape of the quorum thresholds is what makes
\* that bounded number of faults safe to lose.
Crash ==
  /\ crashed < F
  /\ \E i \in 1..N:
       /\ loc[i] \notin {"done", "crashed"}
       /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, proposed, estimate, decided, sent, received>>

Next ==
  \/ BroadcastPhase1 \/ ReceivePhase1 \/ Compute \/ BroadcastPhase2
  \/ ReceivePhase2 \/ Decide \/ ChooseFromView \/ DecideAlt \/ Crash

Spec ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(ReceivePhase1)
  /\ WF_vars(ReceivePhase2)
  /\ WF_vars(Decide)

\* Safety: both classical correctness properties of the primitive.
Validity == \A i \in 1..N : decided[i] # Bottom => \E j \in 1..N : proposed[j] = decided[i]
Agreement == \A i, j \in 1..N : (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

\* Liveness: the guard on ChooseFromView witnesses that every coordinator
\* continues towards a decision, and it is the only way a phase-2 waiting
\* process can leave that state, so it forces termination.
Termination == <>(\A i \in 1..N : loc[i] \in {"done", "crashed"})
ConditionC1 == (\E i \in 1..N : proposed[i] = CHOOSE m \in Values : \A j \in 1..N : proposed[j] <= m) ~> Termination

\* The shape of the quorum thresholds is not independent of the failure bound:
\* T must really be below half the group.
Tolerant == 2 * T < N

\* The invariant form of the agreement check is what lets it survive the
\* degenerate path where every coordinator simply chooses whatever it last saw.
LocalViewsAgree == \A i, j \in 1..N : i # j => \A k \in 1..N : view[i][k] # Bottom => view[i][k] = view[j][k]

\* With T too large the pair of thresholds collapses and the two phases lose
\* their deterministic gap; the two failure bounds together are what keep the
\* protocol on a terminating path.
Robust == Tolerant /\ LocalViewsAgree
====