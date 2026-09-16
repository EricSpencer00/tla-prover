---- MODULE W4Od2m0p4t3 ----
EXTENDS Naturals

CONSTANTS Lanes, Robots, LaneCap, MaxRev

NoLane == "nolane"

VARIABLES level, rev, noteLane, noteRev, holding, slow

vars == <<level, rev, noteLane, noteRev, holding, slow>>

TypeOK ==
  /\ level \in [Lanes -> Nat]
  /\ rev \in [Lanes -> 0..MaxRev]
  /\ noteLane \in [Robots -> Lanes \cup {NoLane}]
  /\ noteRev \in [Robots -> 0..MaxRev]
  /\ holding \in [Robots -> BOOLEAN]
  /\ slow \in [Robots -> BOOLEAN]

\* The whole point of the revision check: a lane is never filled past its cap,
\* not even by a deposit committed from an out-of-date read.
LaneNeverOverfull == \A l \in Lanes : level[l] <= LaneCap

Init ==
  /\ level = [l \in Lanes |-> 0]
  /\ rev = [l \in Lanes |-> 0]
  /\ noteLane = [r \in Robots |-> NoLane]
  /\ noteRev = [r \in Robots |-> 0]
  /\ holding = [r \in Robots |-> FALSE]
  /\ slow = [r \in Robots |-> FALSE]

PickUp(r) ==
  /\ ~holding[r]
  /\ holding' = [holding EXCEPT ![r] = TRUE]
  /\ UNCHANGED <<level, rev, noteLane, noteRev, slow>>

ReadLane(r, l) ==
  /\ holding[r] /\ ~slow[r]
  /\ noteLane[r] = NoLane
  /\ noteLane' = [noteLane EXCEPT ![r] = l]
  /\ noteRev' = [noteRev EXCEPT ![r] = rev[l]]
  /\ UNCHANGED <<level, rev, holding, slow>>

\* Optimistic commit: the note must still match the lane's revision.
Deposit(r, l) ==
  /\ ~slow[r]
  /\ noteLane[r] = l
  /\ noteRev[r] = rev[l]
  /\ rev[l] < MaxRev
  /\ level[l] < LaneCap
  /\ level' = [level EXCEPT ![l] = @ + 1]
  /\ rev' = [rev EXCEPT ![l] = @ + 1]
  /\ noteLane' = [noteLane EXCEPT ![r] = NoLane]
  /\ holding' = [holding EXCEPT ![r] = FALSE]
  /\ UNCHANGED <<noteRev, slow>>

Refused(r, l) ==
  /\ noteLane[r] = l
  /\ noteRev[r] # rev[l]
  /\ noteLane' = [noteLane EXCEPT ![r] = NoLane]
  /\ UNCHANGED <<level, rev, noteRev, holding, slow>>

DrawOff(l) ==
  /\ level[l] > 0
  /\ rev[l] < MaxRev
  /\ level' = [level EXCEPT ![l] = @ - 1]
  /\ rev' = [rev EXCEPT ![l] = @ + 1]
  /\ UNCHANGED <<noteLane, noteRev, holding, slow>>

GoSlow(r) ==
  /\ ~slow[r]
  /\ slow' = [slow EXCEPT ![r] = TRUE]
  /\ UNCHANGED <<level, rev, noteLane, noteRev, holding>>

Resume(r) ==
  /\ slow[r]
  /\ slow' = [slow EXCEPT ![r] = FALSE]
  /\ UNCHANGED <<level, rev, noteLane, noteRev, holding>>

Next ==
  \/ \E r \in Robots : PickUp(r) \/ GoSlow(r) \/ Resume(r)
  \/ \E r \in Robots, l \in Lanes : ReadLane(r, l) \/ Deposit(r, l) \/ Refused(r, l)
  \/ \E l \in Lanes : DrawOff(l)

Spec == Init /\ [][Next]_vars
====