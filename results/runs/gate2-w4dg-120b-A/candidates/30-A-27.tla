---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* A message carries the phase it belongs to, a proposed value, the sender, and
\* an estimated value for phase 2.
Message == [phase: 1..2, val: Values \cup {Bottom}, from: 0..(N-1), est: Values \cup {Bottom}]

Locs == {"broadcast1", "waiting1", "preparing", "broadcast2", "waiting2", "done", "crashed", "choosing"}

VARIABLES loc, view, propose, estimated, decide, crashedCount, sent, recv
vars == <<loc, view, propose, estimated, decide, crashedCount, sent, recv>>

RECURSIVE MaxIn(_, _)
MaxIn(S, f) ==
  IF S = {} THEN Bottom
  ELSE LET x == CHOOSE y \in S : TRUE IN LET y == MaxIn(S \ {x}, f) IN IF y = Bottom THEN f[x] ELSE IF y > f[x] THEN y ELSE f[x]

TypeOK ==
  /\ loc \in [0..(N-1) -> Locs]
  /\ view \in [0..(N-1) -> [0..(N-1) -> Values \cup {Bottom}]]
  /\ propose \in [0..(N-1) -> Values]
  /\ estimated \in [0..(N-1) -> Values \cup {Bottom}]
  /\ decide \in [0..(N-1) -> Values \cup {Bottom}]
  /\ crashedCount \in 0..F
  /\ sent \subseteq Message
  /\ recv \in [0..(N-1) -> SUBSET Message]

Init ==
  /\ loc = [p \in 0..(N-1) |-> "broadcast1"]
  /\ view = [p \in 0..(N-1) |-> [q \in 0..(N-1) |-> Bottom]]
  /\ propose \in [0..(N-1) -> Values]
  /\ estimated = [p \in 0..(N-1) |-> Bottom]
  /\ decide = [p \in 0..(N-1) |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ recv = [p \in 0..(N-1) |-> {}]

BroadcastPhase1(p) ==
  /\ loc[p] = "broadcast1"
  /\ sent' = sent \cup {[phase |-> 1, val |-> propose[p], from |-> p, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![p] = "waiting1"]
  /\ UNCHANGED <<view, propose, estimated, decide, crashedCount, recv>>

\* The physical receive is nondeterministic, but the model assumes weak fairness
\* on it, so it cannot starve.
ReceivePhase1(p, m) ==
  /\ loc[p] = "waiting1"
  /\ m \in sent
  /\ m.phase = 1
  /\ view[p][m.from] = Bottom
  /\ view' = [view EXCEPT ![p][m.from] = m.val]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED <<loc, propose, estimated, decide, crashedCount, sent>>

ComputeEst(p) ==
  /\ loc[p] = "waiting1"
  /\ Cardinality({q \in 0..(N-1) : view[p][q] # Bottom}) >= N - T
  /\ estimated' = [estimated EXCEPT ![p] = MaxIn(0..(N-1), [q \in 0..(N-1) |-> view[p][q]])]
  /\ loc' = [loc EXCEPT ![p] = "broadcast2"]
  /\ UNCHANGED <<view, propose, decide, crashedCount, sent, recv>>

BroadcastPhase2(p) ==
  /\ loc[p] = "broadcast2"
  /\ sent' = sent \cup {[phase |-> 2, val |-> propose[p], from |-> p, est |-> estimated[p]]}
  /\ loc' = [loc EXCEPT ![p] = "waiting2"]
  /\ UNCHANGED <<view, propose, estimated, decide, crashedCount, recv>>

ReceivePhase2(p, m) ==
  /\ loc[p] = "waiting2"
  /\ m \in sent
  /\ m.phase = 2
  /\ view[p][m.from] = Bottom
  /\ view' = [view EXCEPT ![p][m.from] = m.val]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED <<loc, propose, estimated, decide, crashedCount, sent>>

Decide(p) ==
  /\ loc[p] = "waiting2"
  /\ \E e \in Values :
       /\ Cardinality({m \in recv[p] : m.phase = 2 /\ m.est = e}) >= N - T
       /\ decide' = [decide EXCEPT ![p] = e]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, propose, estimated, crashedCount, sent, recv>>

StartChoosing(p) ==
  /\ loc[p] = "waiting2"
  /\ \A e \in Values : Cardinality({m \in recv[p] : m.phase = 2 /\ m.est = e}) < N - T
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, propose, estimated, decide, crashedCount, sent, recv>>

\* Deterministic tie-breaking: the smallest value appearing in the view.
Choose(p) ==
  /\ loc[p] = "choosing"
  /\ \E e \in Values :
       /\ \E q \in 0..(N-1) :
            /\ view[p][q] = e
            /\ \A r \in 0..(N-1) : view[p][r] # Bottom => view[p][r] >= e
            /\ decide' = [decide EXCEPT ![p] = e]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, propose, estimated, crashedCount, sent, recv>>

Crash(p) ==
  /\ loc[p] \notin {"done", "crashed"}
  /\ crashedCount < F
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED <<view, propose, estimated, decide, sent, recv>>

Next ==
  \/ \E p \in 0..(N-1) : BroadcastPhase1(p) \/ ComputeEst(p) \/ BroadcastPhase2(p) \/ Decide(p) \/ StartChoosing(p) \/ Choose(p) \/ Crash(p)
  \/ \E p \in 0..(N-1), m \in Message : ReceivePhase1(p, m) \/ ReceivePhase2(p, m)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in 0..(N-1) : WF_vars(\E m \in Message : ReceivePhase1(p, m))
  /\ \A p \in 0..(N-1) : WF_vars(\E m \in Message : ReceivePhase2(p, m))
  /\ \A p \in 0..(N-1) : WF_vars(ComputeEst(p))
  /\ \A p \in 0..(N-1) : WF_vars(Decide(p))
  /\ \A p \in 0..(N-1) : WF_vars(Choose(p))

\* A decided value was actually proposed by someone.
Validity ==
  \A p \in 0..(N-1) : decide[p] # Bottom => \E q \in 0..(N-1) : propose[q] = decide[p]

Agreement ==
  \A p, q \in 0..(N-1) : (decide[p] # Bottom /\ decide[q] # Bottom) => decide[p] = decide[q]

Termination ==
  <>(\A p \in 0..(N-1) : loc[p] \in {"done", "crashed"})

\* Condition C1: enough processes propose the maximum value.
ConditionC1 ==
  \E S \subseteq 0..(N-1) :
    /\ Cardinality(S) >= F + 1
    /\ \A p \in S : propose[p] = MaxIn(0..(N-1), propose)

CondTermination == ConditionC1 ~> Termination

====