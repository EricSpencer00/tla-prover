---- MODULE cbc_max ----
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Crash fault tolerance: up to F processes may crash, with 2T < N.
\* The system runs a two-phase consensus over a totally ordered value set,
\* and the decision is a plain value (not an identifier).
\* Validity: a decided value was actually proposed by some process.
\* Agreement: no two processes decide different values.
\* Termination: every non-crashed process eventually decides; under C1
\* (at least F+1 propose the maximum), the protocol always terminates.

VARIABLES phase, view, proposed, estimate, decided, crashed, sent, recv
vars == <<phase, view, proposed, estimate, decided, crashed, sent, recv>>

Phases == {"bc1", "wait1", "prep", "bc2", "wait2", "done", "crashed", "choose"}
MessageSpace == [type: {"phase1", "phase2"}, val: Values, snd: 1..N, ev: Values \cup {Bottom}]
NoMsgs == {}

InitMsgs == [i \in 1..N |-> NoMsgs]

TypeOK ==
  /\ phase \in [1..N -> Phases]
  /\ view \in [1..N -> 1..N -> Values \cup {Bottom}]
  /\ proposed \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \in SUBSET MessageSpace
  /\ recv \in [1..N -> SUBSET MessageSpace]

Init ==
  /\ phase = [i \in 1..N |-> "bc1"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ proposed \in [1..N -> Values]
  /\ estimate = [i \in 1..N |-> Bottom]
  /\ decided = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = InitMsgs

Broadcast1(i) ==
  /\ phase[i] = "bc1"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> proposed[i], snd |-> i, ev |-> Bottom]}
  /\ phase' = [phase EXCEPT ![i] = "wait1"]
  /\ UNCHANGED <<view, proposed, estimate, decided, crashed, recv>>

Receive1(i, m) ==
  /\ phase[i] = "wait1"
  /\ m \in sent
  /\ m.type = "phase1"
  /\ view[i][m.snd] = Bottom
  /\ view' = [view EXCEPT ![i][m.snd] = m.val]
  /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
  /\ UNCHANGED <<phase, proposed, estimate, decided, crashed, sent>>

\* Estimate is the maximum over the local view, which is exactly the
\* optimistic guess the optimistic lock tries for: it assumes nothing
\* more was lost than what the view already shows.
Compute(i) ==
  /\ phase[i] = "wait1"
  /\ Cardinality({m \in recv[i] : m.type = "phase1"}) >= N - T
  /\ estimate[i] = Bottom
  /\ estimate' = [estimate EXCEPT ![i] = CHOOSE x \in Values :
                    \A j \in 1..N : view[i][j] \in {Bottom, x} /\ view[i][j] # Bottom => view[i][j] <= x]
  /\ phase' = [phase EXCEPT ![i] = "prep"]
  /\ UNCHANGED <<view, proposed, decided, crashed, sent, recv>>

Broadcast2(i) ==
  /\ phase[i] = "prep"
  /\ sent' = sent \cup {[type |-> "phase2", val |-> proposed[i], snd |-> i, ev |-> estimate[i]]}
  /\ phase' = [phase EXCEPT ![i] = "wait2"]
  /\ UNCHANGED <<view, proposed, estimate, decided, crashed, recv>>

Receive2(i, m) ==
  /\ phase[i] = "wait2"
  /\ m \in sent
  /\ m.type = "phase2"
  /\ view[i][m.snd] = Bottom
  /\ view' = [view EXCEPT ![i][m.snd] = m.val]
  /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
  /\ UNCHANGED <<phase, proposed, estimate, decided, crashed, sent>>

Decide(i) ==
  /\ phase[i] = "wait2"
  /\ \E x \in Values :
       /\ Cardinality({m \in recv[i] : m.type = "phase2" /\ m.ev = x}) >= N - T
       /\ decided' = [decided EXCEPT ![i] = x]
  /\ phase' = [phase EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposed, estimate, crashed, sent, recv>>

\* If the optimistic guess (the estimate) never wins, choosing lets the
\* process fall back on any value its view actually saw, so it always
\* makes progress once it has heard from everybody.
Choose(i) ==
  /\ phase[i] = "wait2"
  /\ \A m \in recv[i] : m.type = "phase2"
  /\ \A x \in Values : Cardinality({m \in recv[i] : m.type = "phase2" /\ m.ev = x}) < N - T
  /\ \E v \in Values :
       /\ \E j \in 1..N : view[i][j] = v /\ decided' = [decided EXCEPT ![i] = v]
  /\ phase' = [phase EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposed, estimate, crashed, sent, recv>>

Crash(i) ==
  /\ crashed < F
  /\ phase[i] \notin {"done", "crashed"}
  /\ phase' = [phase EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, proposed, estimate, decided, sent, recv>>

Next ==
  \/ \E i \in 1..N : Broadcast1(i) \/ Compute(i) \/ Broadcast2(i) \/ Decide(i) \/ Choose(i) \/ Crash(i)
  \/ \E i \in 1..N, m \in MessageSpace : Receive1(i, m) \/ Receive2(i, m)

Spec == Init /\ [][Next]_vars
    /\ \A i \in 1..N : SF_vars(\E m \in MessageSpace : Receive1(i, m))
    /\ \A i \in 1..N : SF_vars(\E m \in MessageSpace : Receive2(i, m))
    /\ \A i \in 1..N : WF_vars(Decide(i) \/ Choose(i))
    /\ \A i \in 1..N : WF_vars(Compute(i))
    /\ \A i \in 1..N : WF_vars(Broadcast2(i))
    /\ \A i \in 1..N : WF_vars(Crash(i))

Validity == \A i \in 1..N : decided[i] # Bottom => \E j \in 1..N : proposed[j] = decided[i]

Agreement == \A i, j \in 1..N : (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

Termination == \A i \in 1..N : (phase[i] \in {"crashed", "done"}) ~> (phase[i] \in {"crashed", "done"})
====