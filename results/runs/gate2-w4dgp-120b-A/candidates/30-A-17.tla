---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME N \in Nat /\ N > 0 /\ T \in Nat /\ F \in Nat /\ 2 * T < N /\ T <= F

\* Stronger than needed, but the model only supports a single crash
\* fault; the termination property under C1 is where the tolerance bound
\* really matters.
ASSUME F <= 1

Locs == {"phase1", "wait1", "prepare", "phase2", "wait2", "done", "crashed", "choosing"}
Msgs == {"phase1", "phase2"}
MaxVal == CHOOSE m \in {x \in Values : \A y \in Values : y <= x}
MaxProposers == {p \in 1..N : p \in MaxVal}

VARIABLES loc, view, proposed, estimate, decided, crashed, sent, rcvd

vars == <<loc, view, proposed, estimate, decided, crashed, sent, rcvd>>

TypeOK ==
  /\ loc \in [1..N -> Locs]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ proposed \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq [type : Msgs, val : Values, from : 1..N]
  /\ rcvd \in [1..N -> SUBSET [type : Msgs, val : Values, from : 1..N]]

Init ==
  /\ loc = [p \in 1..N |-> "phase1"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ proposed \in [1..N -> Values]
  /\ estimate = [p \in 1..N |-> Bottom]
  /\ decided = [p \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ rcvd = [p \in 1..N |-> {}]

\* Phase 1: broadcast own proposal and gather views
SendPhase1(p) ==
  /\ loc[p] = "phase1"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> proposed[p], from |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "wait1"]
  /\ UNCHANGED <<view, proposed, estimate, decided, crashed, rcvd>>

RecvPhase1(p, m) ==
  /\ m \in sent
  /\ m.type = "phase1"
  /\ loc[p] = "wait1"
  /\ m.from \notin rcvd[p]
  /\ view' = [view EXCEPT ![p][m.from] = m.val]
  /\ rcvd' = [rcvd EXCEPT ![p] = @ \cup {m}]
  /\ UNCHANGED <<loc, proposed, estimate, decided, crashed, sent>>

\* Once enough distinct views are collected, compute the max estimate
Prepare(p) ==
  /\ loc[p] = "wait1"
  /\ Cardinality(rcvd[p]) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = Max(Select(view[p], LAMBDA x : x # Bottom))]
  /\ loc' = [loc EXCEPT ![p] = "phase2"]
  /\ UNCHANGED <<view, proposed, decided, crashed, sent, rcvd>>

\* Phase 2: broadcast both the proposal and the estimate
SendPhase2(p) ==
  /\ loc[p] = "phase2"
  /\ sent' = sent \cup {[type |-> "phase2", val |-> proposed[p], from |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "wait2"]
  /\ UNCHANGED <<view, proposed, estimate, decided, crashed, rcvd>>

RecvPhase2(p, m) ==
  /\ m \in sent
  /\ m.type = "phase2"
  /\ loc[p] = "wait2"
  /\ m.from \notin rcvd[p]
  /\ view' = [view EXCEPT ![p][m.from] = m.val]
  /\ rcvd' = [rcvd EXCEPT ![p] = @ \cup {m}]
  /\ UNCHANGED <<loc, proposed, estimate, decided, crashed, sent>>

\* With enough phase-2 messages agreeing on an estimate, decide it
Decide(p) ==
  /\ loc[p] = "wait2"
  /\ \E v \in Values :
       /\ Cardinality({m \in rcvd[p] : m.type = "phase2" /\ m.val = v}) >= N - T
       /\ decided' = [decided EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, proposed, estimate, crashed, sent, rcvd>>

\* If the view is fully collected but no estimate reaches the N-T threshold,
\* the process deterministically picks a visible value and decides it.
Choose(p) ==
  /\ loc[p] = "wait2"
  /\ Cardinality(rcvd[p]) = N
  /\ \A v \in Values : Cardinality({m \in rcvd[p] : m.type = "phase2" /\ m.val = v}) < N - T
  /\ \E w \in Values :
       /\ \E q \in 1..N : view[p][q] = w
       /\ decided' = [decided EXCEPT ![p] = w]
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, proposed, estimate, crashed, sent, rcvd>>

Crash(p) ==
  /\ crashed < F
  /\ crashed' = crashed + 1
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ UNCHANGED <<view, proposed, estimate, decided, sent, rcvd>>

Next ==
  \/ \E p \in 1..N : SendPhase1(p) \/ Prepare(p) \/ SendPhase2(p) \/ Decide(p) \/ Choose(p) \/ Crash(p)
  \/ \E p \in 1..N, m \in sent : RecvPhase1(p, m) \/ RecvPhase2(p, m)

\* Both phases use FIFO-like fairness over receive and broadcast actions so
\* that an empty network empties before the protocol re-broadcasts.
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..N, m \in sent : RecvPhase1(p, m))
  /\ WF_vars(\E p \in 1..N, m \in sent : RecvPhase2(p, m))
  /\ WF_vars(\E p \in 1..N : SendPhase1(p) \/ SendPhase2(p))
  /\ WF_vars(\E p \in 1..N : Prepare(p) \/ Decide(p) \/ Choose(p))
  /\ WF_vars(\E p \in 1..N : Crash(p))

Validity ==
  \A p \in 1..N : decided[p] # Bottom => decided[p] \in Values

Agreement ==
  \A p, q \in 1..N :
    (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

Termination ==
  \A p \in 1..N : loc[p] = "crashed" \/ loc[p] = "done"

ConditionC1 ==
  (MaxProposers # {}) => Termination

====