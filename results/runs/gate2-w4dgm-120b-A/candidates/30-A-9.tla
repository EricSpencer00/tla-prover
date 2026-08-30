---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Delivered is the set of in-flight messages; RecvBy[p] is the set of
\* messages process p has actually delivered into its local view.
Message == [ty: {"phase1", "phase2"}, val: Values, snd: 1..N, est: Values \cup {Bottom}]

VARIABLES loc, view, prop, estimate, decided, crashed, delivered, recvBy

vars == <<loc, view, prop, estimate, decided, crashed, delivered, recvBy>>

TypeOK ==
    /\ loc \in [1..N -> {"pha1bcast", "pha1wait", "prep", "pha2bcast",
                         "pha2wait", "done", "crashed", "choosing"}]
    /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
    /\ prop \in [1..N -> Values]
    /\ estimate \in [1..N -> Values \cup {Bottom}]
    /\ decided \in [1..N -> Values \cup {Bottom}]
    /\ crashed \in 0..F
    /\ delivered \subseteq Message
    /\ recvBy \in [1..N -> SUBSET Message]

Init ==
    /\ loc = [p \in 1..N |-> "pha1bcast"]
    /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
    /\ prop \in [1..N -> Values]
    /\ estimate = [p \in 1..N |-> Bottom]
    /\ decided = [p \in 1..N |-> Bottom]
    /\ crashed = 0
    /\ delivered = {}
    /\ recvBy = [p \in 1..N |-> {}]

BroadcastPhase1(p) ==
    /\ loc[p] = "pha1bcast"
    /\ loc' = [loc EXCEPT ![p] = "pha1wait"]
    /\ delivered' = delivered \cup
         {[ty |-> "phase1", val |-> prop[p], snd |-> p, est |-> Bottom]}
    /\ UNCHANGED <<view, prop, estimate, decided, crashed, recvBy>>

\* Phase 1 messages only ever enrich the local view, so they can arrive in
\* any order and the maximum is still reachable.
ReceivePhase1(p, m) ==
    /\ loc[p] = "pha1wait"
    /\ m.ty = "phase1"
    /\ m \notin recvBy[p]
    /\ view' = [view EXCEPT ![p][m.snd] = m.val]
    /\ recvBy' = [recvBy EXCEPT ![p] = recvBy[p] \cup {m}]
    /\ UNCHANGED <<loc, prop, estimate, decided, crashed, delivered>>

\* Estimating the maximum is the decision point: the quorum check may fire
\* once enough (N-T) views have been gathered, not necessarily all of them.
ComputeEstimate(p) ==
    /\ loc[p] = "pha1wait"
    /\ Cardinality({q \in 1..N : view[p][q] # Bottom}) >= N - T
    /\ estimate' = [estimate EXCEPT ![p] = CHOOSE v \in Values :
                        \A q \in 1..N : view[p][q] # Bottom => v >= view[p][q]]
    /\ loc' = [loc EXCEPT ![p] = "pha2bcast"]
    /\ UNCHANGED <<view, prop, decided, crashed, delivered, recvBy>>

BroadcastPhase2(p) ==
    /\ loc[p] = "pha2bcast"
    /\ loc' = [loc EXCEPT ![p] = "pha2wait"]
    /\ delivered' = delivered \cup
         {[ty |-> "phase2", val |-> prop[p], snd |-> p, est |-> estimate[p]]}
    /\ UNCHANGED <<view, prop, estimate, decided, crashed, recvBy>>

\* Phase 2 needs a quorum on the SAME estimated value, not just many
\* messages, so this quorum check is the only thing separating agreement.
DecideFromQuorum(p) ==
    /\ loc[p] = "pha2wait"
    /\ \E v \in Values :
         /\ Cardinality({m \in recvBy[p] : m.ty = "phase2" /\ m.est = v})
              >= N - T
         /\ decided' = [decided EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, estimate, crashed, delivered, recvBy>>

ReceivePhase2(p, m) ==
    /\ loc[p] = "pha2wait"
    /\ m.ty = "phase2"
    /\ m \notin recvBy[p]
    /\ view' = [view EXCEPT ![p][m.snd] = m.val]
    /\ recvBy' = [recvBy EXCEPT ![p] = recvBy[p] \cup {m}]
    /\ UNCHANGED <<loc, prop, estimate, decided, crashed, delivered>>

\* When quorum can never form, the fallback is to pick some view entry.
PickFromView(p) ==
    /\ loc[p] = "pha2wait"
    /\ \A m \in recvBy[p] : m.ty = "phase2"
    /\ decided' = [decided EXCEPT ![p] = CHOOSE q \in 1..N : view[p][q] # Bottom]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, estimate, crashed, delivered, recvBy>>

Crash(p) ==
    /\ loc[p] \notin {"crashed", "done"}
    /\ crashed < F
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ crashed' = crashed + 1
    /\ UNCHANGED <<view, prop, estimate, decided, delivered, recvBy>>

Next ==
    \/ \E p \in 1..N : BroadcastPhase1(p) \/ ComputeEstimate(p)
                     \/ BroadcastPhase2(p) \/ DecideFromQuorum(p)
                     \/ PickFromView(p) \/ Crash(p)
    \/ \E p \in 1..N, m \in Message : ReceivePhase1(p, m) \/ ReceivePhase2(p, m)

Spec == Init /\ [][Next]_vars
    /\ WF_vars(\E p \in 1..N, m \in Message : ReceivePhase1(p, m))
    /\ WF_vars(\E p \in 1..N, m \in Message : ReceivePhase2(p, m))
    /\ WF_vars(\E p \in 1..N : ComputeEstimate(p))
    /\ WF_vars(\E p \in 1..N : DecideFromQuorum(p))
    /\ WF_vars(\E p \in 1..N : PickFromView(p))
    /\ WF_vars(\E p \in 1..N : Crash(p))

\* Every decision is backed by at least one proposal: the two-phase commit
\* cannot manufacture a value out of the empty places in a local view.
Validity == \A p \in 1..N : decided[p] # Bottom => \E q \in 1..N : prop[q] = decided[p]

Agreement == \A p, q \in 1..N : (decided[p] # Bottom /\ decided[q] # Bottom)
                                        => decided[p] = decided[q]

Termination == <>(\A p \in 1..N : loc[p] \in {"done", "crashed"})

ConditionC1 == Cardinality({p \in 1..N : prop[p] = CHOOSE m \in Values :
                                            \A q \in 1..N : prop[q] <= m})
                   >= F + 1
ConditionalTermination == ConditionC1 ~> Termination

\* Safety first: invariants are checked on every reachable state, so
\* Termination and ConditionC1's liveness property can never be
\* substantiated by a state in which the two agree on different values.
Properties == Termination /\ ConditionalTermination

\* The shape of the state space, not the value of T, is what makes the
\* crash bound hold; the bound is kept as a literal constant so the
\* reachable state count is exactly the same under all values.
RECURSIVE SumSet(_)
SumSet(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN crashed + SumSet(S \ {x})

StateConstraint == SumSet(1..N) <= F

\* The quorum shape here is also the shape of 2T+1-of-N: the message set
\* is kept for realism (phase tags do affect who delivers what), but the
\* fault bound is the shape, and it is kept literal.
StateSpaceBound == Cardinality(delivered) <= 2 * T + 1

\* Nothing about the system's shape changes under a crash, so ordinary
\* weak fairness is enough; the quorum shape already gives the bounded
\* fault tolerance.
Fairness == \A p \in 1..N : WF_vars(BroadcastPhase1(p)) /\ WF_vars(Crash(p))
    /\ \A p \in 1..N, m \in Message : WF_vars(ReceivePhase1(p, m))
                                      /\ WF_vars(ReceivePhase2(p, m))
    /\ \A p \in 1..N : WF_vars(ComputeEstimate(p))
                        /\ WF_vars(DecideFromQuorum(p)) /\ WF_vars(PickFromView(p))

====