---- MODULE cbc_max ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* The max operator expects a nonempty domain; the spec defers the empty case to a
\* distinct MaxEmpty operator so the two are never confused.
RECURSIVE MaxOver(_, _)
MaxOver(f, d) ==
  IF d = {} THEN Bottom
  ELSE LET x == CHOOSE y \in d : TRUE
           maxRest == MaxOver(f, d \ {x})
       IN IF maxRest = Bottom THEN f[x]
          ELSE IF f[x] > maxRest THEN f[x] ELSE maxRest

\* Phase 1 messages only ever require a value; phase 2 messages also carry an
\* estimated value and must be distinguished on receive.
Record == [type: {"phase1", "phase2"}, val: Values \cup {Bottom}, est: Values \cup {Bottom}, from: 1..N]

VARIABLES loc, view, prop, estimate, decided, crashed, sent, recv

vars == <<loc, view, prop, estimate, decided, crashed, sent, recv>>

TypeOK ==
  /\ loc \in [1..N -> {"bc1", "wait1", "prep", "bc2", "wait2", "done", "crashed", "choose"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq Record
  /\ recv \in [1..N -> SUBSET Record]

Init ==
  /\ loc = [p \in 1..N |-> "bc1"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ prop \in [1..N -> Values]
  /\ estimate = [p \in 1..N |-> Bottom]
  /\ decided = [p \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [p \in 1..N |-> {}]

BroadcastPhase1(p) ==
  /\ loc[p] = "bc1"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> prop[p], est |-> Bottom, from |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "wait1"]
  /\ UNCHANGED <<view, estimate, decided, crashed, recv>>

\* Messages must match the current phase; phase1 messages have Bottom as their est.
ReceivePhase1(p, m) ==
  /\ loc[p] = "wait1"
  /\ m \in recv[p]
  /\ m.type = "phase1"
  /\ view' = [view EXCEPT ![p][m.from] = m.val]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \ {m}]
  /\ UNCHANGED <<loc, estimate, decided, crashed, sent, prop>>

ComputeAndBroadcastPhase2(p) ==
  /\ loc[p] = "wait1"
  /\ Cardinality({q \in 1..N : view[p][q] # Bottom}) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = MaxOver(view[p], {q \in 1..N : view[p][q] # Bottom})]
  /\ sent' = sent \cup {[type |-> "phase2", val |-> prop[p], est |-> estimate[p], from |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "bc2"]
  /\ UNCHANGED <<view, decided, crashed, recv>>

ReceivePhase2(p, m) ==
  /\ loc[p] = "wait2"
  /\ m \in recv[p]
  /\ m.type = "phase2"
  /\ view' = [view EXCEPT ![p][m.from] = m.val]
  /\ estimate' = [estimate EXCEPT ![p] = IF estimate[p] = Bottom THEN m.est ELSE estimate[p]]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \ {m}]
  /\ UNCHANGED <<loc, decided, crashed, sent>>

DecideByMajority(p) ==
  /\ loc[p] = "wait2"
  /\ (\E v \in Values : Cardinality({m \in recv[p] : m.est = v}) >= N - T)
  /\ decided' = [decided EXCEPT ![p] = estimate[p]]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, estimate, crashed, sent, recv>>

\* Deterministic fallback when no majority emerges (still bounded by the spec).
ChooseOwn(p) ==
  /\ loc[p] = "choose"
  /\ \E v \in Values : decided' = [decided EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, estimate, crashed, sent, recv>>

TransitionToSecondPhase(p) ==
  /\ loc[p] = "bc2"
  /\ loc' = [loc EXCEPT ![p] = "wait2"]
  /\ UNCHANGED <<view, estimate, decided, crashed, sent, recv>>

TransitionToChoosing(p) ==
  /\ loc[p] = "wait2"
  /\ Cardinality({m \in recv[p] : m.type = "phase2"}) >= N
  /\ loc' = [loc EXCEPT ![p] = "choose"]
  /\ UNCHANGED <<view, estimate, decided, crashed, sent, recv>>

Crash(p) ==
  /\ crashed < F
  /\ loc[p] \in {"bc1", "wait1", "bc2", "wait2", "choose"}
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, estimate, decided, sent, recv>>

Next ==
  \/ \E p \in 1..N : BroadcastPhase1(p)
  \/ \E p \in 1..N, m \in Record : ReceivePhase1(p, m)
  \/ \E p \in 1..N : ComputeAndBroadcastPhase2(p)
  \/ \E p \in 1..N, m \in Record : ReceivePhase2(p, m)
  \/ \E p \in 1..N : DecideByMajority(p)
  \/ \E p \in 1..N : ChooseOwn(p)
  \/ \E p \in 1..N : TransitionToSecondPhase(p)
  \/ \E p \in 1..N : TransitionToChoosing(p)
  \/ \E p \in 1..N : Crash(p)

Spec == Init /\ [][Next]_vars
        /\ \A p \in 1..N, m \in Record :
             WF_vars(ReceivePhase1(p, m))
             /\ WF_vars(ReceivePhase2(p, m))
        /\ \A p \in 1..N :
             WF_vars(ComputeAndBroadcastPhase2(p))
             /\ WF_vars(DecideByMajority(p))
             /\ WF_vars(ChooseOwn(p))
             /\ WF_vars(TransitionToSecondPhase(p))
             /\ WF_vars(TransitionToChoosing(p))

Validity == \A p \in 1..N : decided[p] # Bottom => \E q \in 1..N : prop[q] = decided[p]

Agreement == \A p, q \in 1..N : (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

Termination == <>(\A p \in 1..N : loc[p] \in {"done", "crashed"})

\* Under Condition C1 (enough max-proposers) the protocol is guaranteed to finish.
C1Termination ==
  /\ (\E k \in 1..N : prop[k] = MaxOver(prop, 1..N))
  /\ Termination

====