---- MODULE W4Od6m2p2t3 ----
EXTENDS Naturals
CONSTANTS f1, f2
Floors == {f1, f2}
TOTAL == 2

VARIABLES waiting, car, resv, ph, ready
vars == <<waiting, car, resv, ph, ready>>

Init ==
  /\ waiting = [f \in Floors |-> 1]
  /\ car = 0
  /\ resv = [f \in Floors |-> 0]
  /\ ph = "idle"
  /\ ready = [f \in Floors |-> FALSE]

Begin ==
  /\ ph = "idle"
  /\ ph' = "voting"
  /\ ready' = [f \in Floors |-> FALSE]
  /\ UNCHANGED <<waiting, car, resv>>

Prepare(f) ==
  /\ ph = "voting"
  /\ ~ready[f]
  /\ waiting[f] >= 1
  /\ waiting' = [waiting EXCEPT ![f] = @ - 1]
  /\ resv' = [resv EXCEPT ![f] = 1]
  /\ ready' = [ready EXCEPT ![f] = TRUE]
  /\ UNCHANGED <<car, ph>>

PrepareEmpty(f) ==
  /\ ph = "voting"
  /\ ~ready[f]
  /\ waiting[f] = 0
  /\ ready' = [ready EXCEPT ![f] = TRUE]
  /\ UNCHANGED <<waiting, car, resv, ph>>

Commit ==
  /\ ph = "voting"
  /\ \A f \in Floors : ready[f]
  /\ car' = car + resv[f1] + resv[f2]
  /\ resv' = [f \in Floors |-> 0]
  /\ ph' = "committed"
  /\ UNCHANGED <<waiting, ready>>

Reset ==
  /\ ph = "committed"
  /\ ph' = "idle"
  /\ UNCHANGED <<waiting, car, resv, ready>>

Next ==
  \/ Begin \/ Commit \/ Reset
  \/ \E f \in Floors : Prepare(f) \/ PrepareEmpty(f)
Spec == Init /\ [][Next]_vars

PassengersConserved == (waiting[f1] + waiting[f2]) + (resv[f1] + resv[f2]) + car = TOTAL
===