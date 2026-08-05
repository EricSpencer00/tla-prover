---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom
ASSUME N \in Nat /\ N > 0 /\ T \in Nat /\ F \in Nat /\ T <= F /\ 2 * T < N

\* Messages carry the sending phase, a value, and a sender. Phase 2 adds an
\* estimated value, so a message is tagged with its phase.
Msg == [type : {"a", "b"}, val : Values \cup {Bottom}, snd : 1..N]

VARIABLES pc, view, propose, est, decision, crashed, sent, inbox
vars == <<pc, view, propose, est, decision, crashed, sent, inbox>>

MaxV == CHOOSE x \in Values : \A y \in Values : y <= x

TypeOK ==
    /\ pc \in [1..N -> {"phase1_broadcast", "phase1_wait", "preparing",
                        "phase2_broadcast", "phase2_wait", "done", "crashed",
                        "choosing"}]
    /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
    /\ propose \in [1..N -> Values]
    /\ est \in [1..N -> Values \cup {Bottom}]
    /\ decision \in [1..N -> Values \cup {Bottom}]
    /\ crashed \in 0..F
    /\ sent \subseteq Msg
    /\ inbox \in [1..N -> SUBSET Msg]

Init ==
    /\ pc = [i \in 1..N |-> "phase1_broadcast"]
    /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
    /\ propose \in [1..N -> Values]
    /\ est = [i \in 1..N |-> Bottom]
    /\ decision = [i \in 1..N |-> Bottom]
    /\ crashed = 0
    /\ sent = {}
    /\ inbox = [i \in 1..N |-> {}]

\* Phase 1 broadcast: each process emits its own proposal.
B1(i) ==
    /\ pc[i] = "phase1_broadcast"
    /\ sent' = sent \cup {[type |-> "a", val |-> propose[i], snd |-> i]}
    /\ pc' = [pc EXCEPT ![i] = "phase1_wait"]
    /\ UNCHANGED <<view, propose, est, decision, crashed, inbox>>

\* Receiving a phase-1 message updates the local view of the sender's value.
R1(i) ==
    /\ \E m \in inbox[i] :
        /\ m.type = "a"
        /\ view' = [view EXCEPT ![i][m.snd] = m.val]
    /\ UNCHANGED <<pc, propose, est, decision, crashed, sent, inbox>>

\* After phase 1, with enough views collected, compute the estimate and move on.
P1(i) ==
    /\ pc[i] = "phase1_wait"
    /\ Cardinality({j \in 1..N : view[i][j] # Bottom}) >= N - T
    /\ LET mx == CHOOSE x \in Values :
                     \A y \in Values : (\E j \in 1..N : view[i][j] = y) => y <= x
       IN est' = [est EXCEPT ![i] = mx]
    /\ pc' = [pc EXCEPT ![i] = "phase2_broadcast"]
    /\ UNCHANGED <<view, propose, decision, crashed, sent, inbox>>

\* Phase 2 broadcast: each process emits its proposal and its estimate.
B2(i) ==
    /\ pc[i] = "phase2_broadcast"
    /\ sent' = sent \cup {[type |-> "b", val |-> propose[i], snd |-> i]}
    /\ pc' = [pc EXCEPT ![i] = "phase2_wait"]
    /\ UNCHANGED <<view, propose, est, decision, crashed, inbox>>

AgreeOn(v) == Cardinality({j \in 1..N : \E m \in inbox[j] : m.type = "b" /\ m.val = v})

\* Receiving phase-2 messages and deciding once a sufficient majority agrees.
D2(i) ==
    /\ pc[i] = "phase2_wait"
    /\ \E v \in Values : AgreeOn(v) >= N - T
    /\ decision' = [decision EXCEPT ![i] = v]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<view, propose, est, crashed, sent, inbox>>

\* When no single estimate reaches the majority, the process deterministically
\* chooses some value it knows about and decides it.
Choose(i) ==
    /\ pc[i] = "choosing"
    /\ \E v \in Values :
        /\ \E j \in 1..N : view[i][j] = v
        /\ decision' = [decision EXCEPT ![i] = v]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<view, propose, est, crashed, sent, inbox>>

\* A crashed process stops participating, bounded by the tolerance.
Crash ==
    /\ crashed < F
    /\ crashed' = crashed + 1
    /\ UNCHANGED <<pc, view, propose, est, decision, sent, inbox>>

Next ==
    \/ \E i \in 1..N : B1(i) \/ R1(i) \/ P1(i) \/ B2(i) \/ D2(i) \/ Choose(i)
    \/ Crash

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(R1(1)) /\ WF_vars(D2(1))
    /\ WF_vars(R1(2)) /\ WF_vars(D2(2))
    /\ WF_vars(R1(3)) /\ WF_vars(D2(3))
    /\ WF_vars(R1(4)) /\ WF_vars(D2(4))

\* Validity: any decision output was actually proposed by some process.
Validity == \A i \in 1..N : decision[i] # Bottom => \E j \in 1..N : propose[j] = decision[i]

\* Agreement: no two processes ever decide different values.
Agreement == \A i, j \in 1..N : (decision[i] # Bottom /\ decision[j] # Bottom)
                                 => decision[i] = decision[j]

\* Termination: every process eventually crashes or finishes.
Termination == \A i \in 1..N : <>(pc[i] = "crashed" \/ pc[i] = "done")

\* Conditional termination: the majority condition on the maximum value forces
\* every process to finish.
CondC1Termination ==
    (\A i \in 1..N : (propose[i] = MaxV) >= F + 1)
    => (\A i \in 1..N : <>(pc[i] = "crashed" \/ pc[i] = "done"))

====