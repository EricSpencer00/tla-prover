---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    N, T, F, Values, Bottom

\* The value set is totally ordered, and everything must be distinct from Bottom.
Assume /\ N \in Nat /\ N > 0
       /\ T \in Nat /\ F \in Nat /\ F <= T /\ 2 * T < N
       /\ Values \subseteq (Nat \ {Bottom})

Msgs == [kind: {"phase1", "phase2"}, val: Values \cup {Bottom}, est: Values \cup {Bottom}, from: 0..(N - 1)]

VARIABLES phase, view, prop, est, decided, crashed, sent, recv

vars == <<phase, view, prop, est, decided, crashed, sent, recv>>

TypeOK ==
    /\ phase \in [0..(N - 1) -> {"phase1", "wait1", "phase2", "wait2", "done", "crashed", "choose"}]
    /\ view \in [0..(N - 1), 0..(N - 1) -> Values \cup {Bottom}]
    /\ prop \in [0..(N - 1) -> Values]
    /\ est \in [0..(N - 1) -> Values \cup {Bottom}]
    /\ decided \in [0..(N - 1) -> Values \cup {Bottom}]
    /\ crashed \in 0..F
    /\ sent \subseteq Msgs
    /\ recv \in [0..(N - 1) -> SUBSET Msgs]

Init ==
    /\ phase = [p \in 0..(N - 1) |-> "phase1"]
    /\ view = [p \in 0..(N - 1), q \in 0..(N - 1) |-> Bottom]
    /\ \E v \in [0..(N - 1) -> Values] :
           prop = v
    /\ est = [p \in 0..(N - 1) |-> Bottom]
    /\ decided = [p \in 0..(N - 1) |-> Bottom]
    /\ crashed = 0
    /\ sent = {}
    /\ recv = [p \in 0..(N - 1) |-> {}]

BroadcastPhase1(p) ==
    /\ phase[p] = "phase1"
    /\ sent' = sent \cup {[kind |-> "phase1", val |-> prop[p], est |-> Bottom, from |-> p]}
    /\ phase' = [phase EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<view, prop, est, decided, crashed, recv>>

RecvMsgs(p) ==
    /\ phase[p] \in {"wait1", "wait2"}
    /\ \E m \in recv[p] :
         /\ m.kind = phase[p]
         /\ view' = [view EXCEPT ![p][m.from] = m.val]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \ {m}]
    /\ UNCHANGED <<phase, prop, est, decided, crashed, sent>>

StandardTransition(p) ==
    /\ phase[p] = "wait1"
    /\ Cardinality({q \in 0..(N - 1) : view[p][q] # Bottom}) >= N - T
    /\ est' = [est EXCEPT ![p] = CHOOSE v \in Values :
                   \E w \in Values : v = CHOOSE x \in Values : \A y \in Values : (x \in {view[p][q] : q \in 0..(N - 1)} /\ y \in {view[p][q] : q \in 0..(N - 1)}) => x >= y]
    /\ phase' = [phase EXCEPT ![p] = "phase2"]
    /\ UNCHANGED <<view, prop, decided, crashed, sent, recv>>

BroadcastPhase2(p) ==
    /\ phase[p] = "phase2"
    /\ sent' = sent \cup {[kind |-> "phase2", val |-> prop[p], est |-> est[p], from |-> p]}
    /\ phase' = [phase EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<view, prop, est, decided, crashed, recv>>

StandardDecide(p) ==
    /\ phase[p] = "wait2"
    /\ \E v \in Values :
         /\ {q \in 0..(N - 1) : \E m \in recv[p] : m.kind = "phase2" /\ m.est = v} >= N - T
         /\ decided' = [decided EXCEPT ![p] = v]
    /\ phase' = [phase EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

Choose(p) ==
    /\ phase[p] = "wait2"
    /\ \A q \in 0..(N - 1) : \E m \in recv[p] : m.kind = "phase2" /\ m.from = q
    /\ Cardinality({q \in 0..(N - 1) : view[p][q] # Bottom}) < N - T
    /\ phase' = [phase EXCEPT ![p] = "choose"]
    /\ UNCHANGED <<view, prop, est, decided, crashed, sent, recv>>

DeterministicChoose(p) ==
    /\ phase[p] = "choose"
    /\ decided' = [decided EXCEPT ![p] = view[p][CHOOSE q \in 0..(N - 1) : view[p][q] # Bottom]]
    /\ phase' = [phase EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

Crash(p) ==
    /\ phase[p] \notin {"crashed", "done"}
    /\ crashed < F
    /\ phase' = [phase EXCEPT ![p] = "crashed"]
    /\ crashed' = crashed + 1
    /\ UNCHANGED <<view, prop, est, decided, sent, recv>>

Next ==
    \/ \E p \in 0..(N - 1) : BroadcastPhase1(p)
    \/ \E p \in 0..(N - 1) : RecvMsgs(p)
    \/ \E p \in 0..(N - 1) : StandardTransition(p)
    \/ \E p \in 0..(N - 1) : BroadcastPhase2(p)
    \/ \E p \in 0..(N - 1) : StandardDecide(p)
    \/ \E p \in 0..(N - 1) : Choose(p)
    \/ \E p \in 0..(N - 1) : DeterministicChoose(p)
    \/ \E p \in 0..(N - 1) : Crash(p)

Spec == Init /\ [][Next]_vars
        /\ \A p \in 0..(N - 1) : WF_vars(RecvMsgs(p))
        /\ \A p \in 0..(N - 1) : WF_vars(StandardTransition(p))
        /\ \A p \in 0..(N - 1) : WF_vars(StandardDecide(p))
        /\ \A p \in 0..(N - 1) : WF_vars(DeterministicChoose(p))

Validity == \A p \in 0..(N - 1) : decided[p] # Bottom => \E q \in 0..(N - 1) : prop[q] = decided[p]

Agreement == \A a, b \in 0..(N - 1) : (decided[a] # Bottom /\ decided[b] # Bottom) => decided[a] = decided[b]

Termination == <>(\A p \in 0..(N - 1) : phase[p] \in {"done", "crashed"})

ConditionC1 == \A p \in 0..(N - 1) :
                  (decided[p] # Bottom \/ phase[p] = "crashed") =>
                      (\E q \in 0..(N - 1) : prop[q] >= decided[p])

====