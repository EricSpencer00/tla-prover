---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    N,          \* number of processes
    T,          \* max tolerated crash faults
    F,          \* max actual crash faults (F <= T)
    Values,     \* finite totally ordered set of proposal values
    Bottom      \* special bottom value, not in Values

\* ---------- State Variables ----------
VARIABLES
    phase,          \* mapping each process to its control location
    localView,      \* N->(N->Values \cup {Bottom}) matrix of observed values
    proposed,       \* mapping each process to its initial proposal
    estimate,       \* mapping each process to its current estimate (Bottom or a value)
    decision,       \* mapping each process to its decided value (Bottom if none)
    crashedCount,   \* number of processes that have crashed so far
    sent,           \* set of messages that have been broadcast
    received        \* mapping each process to the set of messages it has received

\* ---------- Enumerated control locations ----------
PhaseBC1 == "bc1"          \* broadcasting phase 1
PhaseW1  == "w1"           \* waiting for phase 1 messages
PhaseBC2 == "bc2"          \* broadcasting phase 2
PhaseW2  == "w2"           \* waiting for phase 2 messages
PhaseC   == "c"            \* choosing state
PhaseDone== "done"         \* finished with a decision
PhaseCrashed == "crashed"  \* crashed

\* ---------- Message definition ----------
Message == [type : {"phase1","phase2"},
            sender : 1..N,
            prop   : Values,
            est    : Values \cup {Bottom}]

\* ---------- Helper definitions ----------
MaxInView(vs) ==
    IF \E x \in vs: x # Bottom
    THEN \CHOOSE m \in vs : \A y \in vs : (y # Bottom) => m >= y
    ELSE Bottom

AllProcs == 1..N

\* ---------- Initial state ----------
Init ==
    /\ phase = [p \in AllProcs |-> PhaseBC1]
    /\ proposed = [p \in AllProcs |-> CHOOSE v \in Values : TRUE]
    /\ localView = [p \in AllProcs |-> [q \in AllProcs |-> Bottom]]
    /\ estimate = [p \in AllProcs |-> Bottom]
    /\ decision = [p \in AllProcs |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ received = [p \in AllProcs |-> {}]

\* ---------- Actions ----------
BroadcastPhase1(p) ==
    /\ phase[p] = PhaseBC1
    /\ sent' = sent \cup {[type |-> "phase1",
                           sender |-> p,
                           prop   |-> proposed[p],
                           est    |-> Bottom}]
    /\ phase' = [phase EXCEPT ![p] = PhaseW1]
    /\ UNCHANGED <<localView, proposed, estimate, decision,
                    crashedCount, received>>

ReceivePhase1(p, m) ==
    /\ phase[p] = PhaseW1
    /\ m \in sent
    /\ m.type = "phase1"
    /\ localView' = [localView EXCEPT ![p][m.sender] = m.prop]
    /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
    /\ UNCHANGED <<phase, proposed, estimate, decision,
                    crashedCount, sent>>

ReadyForPhase2(p) ==
    /\ phase[p] = PhaseW1
    /\ Cardinality({ m \in received[p] : m.type = "phase1" }) >= N - T
    /\ estimate' = [estimate EXCEPT ![p] = MaxInView({ localView[p][q] : q \in AllProcs })]
    /\ phase' = [phase EXCEPT ![p] = PhaseBC2]
    /\ UNCHANGED <<localView, proposed, decision,
                    crashedCount, sent, received>>

BroadcastPhase2(p) ==
    /\ phase[p] = PhaseBC2
    /\ sent' = sent \cup {[type |-> "phase2",
                           sender |-> p,
                           prop   |-> proposed[p],
                           est    |-> estimate[p]}]
    /\ phase' = [phase EXCEPT ![p] = PhaseW2]
    /\ UNCHANGED <<localView, proposed, estimate, decision,
                    crashedCount, received>>

ReceivePhase2(p, m) ==
    /\ phase[p] = PhaseW2
    /\ m \in sent
    /\ m.type = "phase2"
    /\ localView' = [localView EXCEPT ![p][m.sender] = m.est]
    /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
    /\ UNCHANGED <<phase, proposed, estimate, decision,
                    crashedCount, sent>>

DecideFromW2(p) ==
    /\ phase[p] = PhaseW2
    /\ \E v \in Values :
          Cardinality({ m \in received[p] :
                         m.type = "phase2" /\ m.est = v }) >= N - T
    /\ decision' = [decision EXCEPT ![p] = CHOOSE v \in Values :
                        Cardinality({ m \in received[p] :
                                       m.type = "phase2" /\ m.est = v }) >= N - T]
    /\ phase' = [phase EXCEPT ![p] = PhaseDone]
    /\ UNCHANGED <<localView, proposed, estimate, crashedCount, sent, received>>

MoveToChoosing(p) ==
    /\ phase[p] = PhaseW2
    /\ \A v \in Values :
          Cardinality({ m \in received[p] :
                         m.type = "phase2" /\ m.est = v }) < N - T
    /\ Cardinality({ m \in received[p] : m.type = "phase2" }) = N
    /\ phase' = [phase EXCEPT ![p] = PhaseC]
    /\ UNCHANGED <<localView, proposed, estimate, decision,
                    crashedCount, sent, received>>

ChooseAndDecide(p) ==
    /\ phase[p] = PhaseC
    /\ \E v \in Values :
          \E q \in AllProcs :
            (v = localView[p][q]) \/ (v = proposed[p])
    /\ decision' = [decision EXCEPT ![p] = CHOOSE v \in Values :
                        \E q \in AllProcs : v = localView[p][q] \/ v = proposed[p]]
    /\ phase' = [phase EXCEPT ![p] = PhaseDone]
    /\ UNCHANGED <<localView, proposed, estimate, crashedCount, sent, received>>

Crash(p) ==
    /\ crashedCount < F
    /\ phase[p] # PhaseCrashed
    /\ phase' = [phase EXCEPT ![p] = PhaseCrashed]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED <<localView, proposed, estimate, decision,
                    sent, received>>

\* ---------- Weak fairness of enabled actions ----------
Next ==
    \/ \E p \in AllProcs : BroadcastPhase1(p)
    \/ \E p \in AllProcs, m \in sent : ReceivePhase1(p, m)
    \/ \E p \in AllProcs : ReadyForPhase2(p)
    \/ \E p \in AllProcs : BroadcastPhase2(p)
    \/ \E p \in AllProcs, m \in sent : ReceivePhase2(p, m)
    \/ \E p \in AllProcs : DecideFromW2(p)
    \/ \E p \in AllProcs : MoveToChoosing(p)
    \/ \E p \in AllProcs : ChooseAndDecide(p)
    \/ \E p \in AllProcs : Crash(p)

\* ---------- Specification ----------
Spec == Init /\ [][Next]_<<phase, localView, proposed, estimate,
                         decision, crashedCount, sent, received>>

\* ---------- Type correctness ----------
TypeOK ==
    /\ phase \in [AllProcs -> {PhaseBC1, PhaseW1, PhaseBC2,
                              PhaseW2, PhaseC, PhaseDone, PhaseCrashed}]
    /\ localView \in [AllProcs -> [AllProcs -> (Values \cup {Bottom})]]
    /\ proposed \in [AllProcs -> Values]
    /\ estimate \in [AllProcs -> (Values \cup {Bottom})]
    /\ decision \in [AllProcs -> (Values \cup {Bottom})]
    /\ crashedCount \in Nat
    /\ sent \subseteq Message
    /\ received \in [AllProcs -> SUBSET Message]

\* ---------- Safety properties ----------
Validity ==
    \A p \in AllProcs :
        decision[p] # Bottom => decision[p] \in Values

Agreement ==
    \A p, q \in AllProcs :
        /\ decision[p] # Bottom
        /\ decision[q] # Bottom
        => decision[p] = decision[q]

\* ---------- Liveness (not required as invariant, but useful) ----------
Termination ==
    \A p \in AllProcs :
        phase[p] \in {PhaseDone, PhaseCrashed}

\* ---------- THEOREM (optional) ----------
THEOREM Spec => []Validity
THEOREM Spec => []Agreement

====