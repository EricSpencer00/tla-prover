---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F, Values, Bottom

ASSUME N \in Nat /\ N > 0 /\ T \in Nat /\ F \in Nat /\ Values \subseteq Nat /\ Bottom \notin Values

\* 2T < N is the resilience condition underlying Condition C1; the protocol
\* needs strictly fewer than a third of the processes to be trusted.
ASSUME 2 * T < N /\ F <= T

VARIABLES loc, view, proposed, est, decision, crashed, sent, rcvd

vars == <<loc, view, proposed, est, decision, crashed, sent, rcvd>>

Phase1 == "phase1"
Phase2 == "phase2"
Done == "done"
Choosing == "choosing"
Crashed == "crashed"

Locs == {Phase1, Phase2, Done, Choosing, Crashed}

Types == [type : {Phase1, Phase2}, value : Values \cup {Bottom}, sender : 0..(N-1), evalue : Values \cup {Bottom}]
Messages == Types

FromSet(ms) == {m.sender : m \in ms}

MaxInSet(S) == LET g[T \in SUBSET S] ==
                   IF T = {} THEN Bottom
                   ELSE LET x == CHOOSE y \in T : TRUE
                        IN IF g[T \ {x}] = Bottom THEN x ELSE IF x > g[T \ {x}] THEN x ELSE g[T \ {x}]
               IN g[S]

Init == /\ loc = [i \in 0..(N-1) |-> Phase1]
        /\ view = [i \in 0..(N-1), j \in 0..(N-1) |-> Bottom]
        /\ \E f \in [0..(N-1) -> Values] : proposed = f
        /\ est = [i \in 0..(N-1) |-> Bottom]
        /\ decision = [i \in 0..(N-1) |-> Bottom]
        /\ crashed = 0
        /\ sent = {}
        /\ rcvd = [i \in 0..(N-1) |-> {}]

BroadcastPhase1(i) == /\ loc[i] = Phase1
                      /\ sent' = sent \cup {[type |-> Phase1, value |-> proposed[i], sender |-> i, evalue |-> Bottom]}
                      /\ loc' = [loc EXCEPT ![i] = Phase2]
                      /\ UNCHANGED <<view, proposed, est, decision, crashed, rcvd>>

ReceivePhase1(i, m) == /\ loc[i] = Phase2
                       /\ m \in sent
                       /\ m.type = Phase1
                       /\ i # m.sender
                       /\ view[i][m.sender] = Bottom
                       /\ view' = [view EXCEPT ![i][m.sender] = m.value]
                       /\ rcvd' = [rcvd EXCEPT ![i] = rcvd[i] \cup {m}]
                       /\ UNCHANGED <<loc, proposed, est, decision, crashed, sent>>

\* After Phase 1, the process takes the maximum value it has learned so far.
StartPhase2(i) == /\ loc[i] = Phase2
                  /\ Cardinality(FromSet(rcvd[i])) >= N - T
                  /\ loc' = [loc EXCEPT ![i] = Phase1]
                  /\ est' = [est EXCEPT ![i] = MaxInSet({view[i][j] : j \in 0..(N-1)} \cup {proposed[i]})]
                  /\ UNCHANGED <<view, proposed, decision, crashed, sent, rcvd>>

BroadcastPhase2(i) == /\ loc[i] = Phase1
                      /\ sent' = sent \cup {[type |-> Phase2, value |-> proposed[i], evalue |-> est[i], sender |-> i]}
                      /\ loc' = [loc EXCEPT ![i] = Phase2]
                      /\ UNCHANGED <<view, proposed, est, decision, crashed, rcvd>>

\* The consensus condition: enough processes must agree on the same estimate.
Decide(i) == /\ loc[i] = Phase2
             /\ \E v \in Values :
                  /\ Cardinality({m \in rcvd[i] : m.type = Phase2 /\ m.evalue = v}) >= N - T
                  /\ decision' = [decision EXCEPT ![i] = v]
             /\ loc' = [loc EXCEPT ![i] = Done]
             /\ UNCHANGED <<view, proposed, est, crashed, sent, rcvd>>

\* Deterministic fallback: if no estimate reached the N-T threshold, the
\* process picks a value it already knows from its local view.
Choose(i) == /\ loc[i] = Phase2
             /\ Cardinality(FromSet(rcvd[i])) >= N
             /\ \E v \in Values :
                  /\ \E j \in 0..(N-1) : view[i][j] = v
                  /\ decision' = [decision EXCEPT ![i] = v]
             /\ loc' = [loc EXCEPT ![i] = Choosing]
             /\ UNCHANGED <<view, proposed, est, crashed, sent, rcvd>>

Crash(i) == /\ loc[i] \notin {Done, Crashed}
            /\ crashed < F
            /\ crashed' = crashed + 1
            /\ loc' = [loc EXCEPT ![i] = Crashed]
            /\ UNCHANGED <<view, proposed, est, decision, sent, rcvd>>

Next == \E i \in 0..(N-1) :
          BroadcastPhase1(i) \/ StartPhase2(i) \/ BroadcastPhase2(i) \/ Decide(i) \/ Choose(i) \/ Crash(i)
          \/ \E m \in Messages : ReceivePhase1(i, m)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(\E i \in 0..(N-1) : ReceivePhase1(i, CHOOSE m \in sent : TRUE))
        /\ WF_vars(\E i \in 0..(N-1) : BroadcastPhase1(i))
        /\ WF_vars(\E i \in 0..(N-1) : StartPhase2(i))
        /\ WF_vars(\E i \in 0..(N-1) : BroadcastPhase2(i))
        /\ WF_vars(\E i \in 0..(N-1) : Decide(i))
        /\ WF_vars(\E i \in 0..(N-1) : Choose(i))

\* No false values: whatever a process decides was actually proposed by some
\* participant.
TypeOK == /\ loc \in [0..(N-1) -> Locs]
          /\ view \in [0..(N-1), 0..(N-1) -> Values \cup {Bottom}]
          /\ est \in [0..(N-1) -> Values \cup {Bottom}]
          /\ decision \in [0..(N-1) -> Values \cup {Bottom}]

Validity == \A i \in 0..(N-1) : decision[i] # Bottom => \E j \in 0..(N-1) : decision[i] = proposed[j]

Agreement == \A i, j \in 0..(N-1) : (decision[i] # Bottom /\ decision[j] # Bottom) => decision[i] = decision[j]

Terminate == <>(\A i \in 0..(N-1) : loc[i] \in {Done, Crashed})

\* Conditional termination: if enough processes propose the maximum, the
\* protocol necessarily reaches a decision.
ConditionC1 == Cardinality({i \in 0..(N-1) : proposed[i] = MaxInSet(Values)}) >= F + 1

CondTerminate == ConditionC1 ~> Terminate

INVARIANT TypeOK
PROPERTY Validity
PROPERTY Agreement
PROPERTY Terminate
PROPERTY CondTerminate

====