---- MODULE W4Od9m8p4t4 ----
EXTENDS Naturals

CONSTANTS Feeders, HardCap

VARIABLES load, ceiling, coarseHeld, fineHeld

Vars == <<load, ceiling, coarseHeld, fineHeld>>

NoFeeder == "none"

\* Sum committed load across all feeders (recursive fold over a finite set).
RECURSIVE SumLoad(_)
SumLoad(S) == IF S = {} THEN 0
              ELSE LET f == CHOOSE x \in S : TRUE
                   IN load[f] + SumLoad(S \ {f})
TotalLoad == SumLoad(Feeders)

TypeOK ==
  /\ load \in [Feeders -> 0..HardCap]
  /\ ceiling \in 0..HardCap
  /\ coarseHeld \in BOOLEAN
  /\ fineHeld \in Feeders \cup {NoFeeder}

Init ==
  /\ load = [f \in Feeders |-> 0]
  /\ ceiling = HardCap
  /\ coarseHeld = FALSE
  /\ fineHeld = NoFeeder

\* Coarse region lock must be taken before any fine per-feeder lock, and only
\* when some feeder actually has something to shed or room to restore into.
AcquireCoarse ==
  /\ ~coarseHeld
  /\ fineHeld = NoFeeder
  /\ \E f \in Feeders : load[f] > 0 \/ TotalLoad + 1 <= ceiling
  /\ coarseHeld' = TRUE
  /\ UNCHANGED <<load, ceiling, fineHeld>>

\* Only take the fine lock on a feeder that can actually be acted on next
\* (something to shed, or headroom under the ceiling to restore into) --
\* otherwise a badly-chosen feeder could wedge the lock chain forever.
AcquireFine(f) ==
  /\ coarseHeld
  /\ fineHeld = NoFeeder
  /\ load[f] > 0 \/ TotalLoad + 1 <= ceiling
  /\ fineHeld' = f
  /\ UNCHANGED <<load, ceiling, coarseHeld>>

\* Committing a shed and releasing both locks happen in one atomic step.
ShedRelease(f) ==
  /\ fineHeld = f
  /\ load[f] > 0
  /\ load' = [load EXCEPT ![f] = load[f] - 1]
  /\ coarseHeld' = FALSE
  /\ fineHeld' = NoFeeder
  /\ UNCHANGED ceiling

\* Restoring load is bounded by the CURRENT ceiling, not the hard limit --
\* so a fresh ceiling drop can never be worsened by a concurrent restore.
RestoreRelease(f) ==
  /\ fineHeld = f
  /\ TotalLoad + 1 <= ceiling
  /\ load' = [load EXCEPT ![f] = load[f] + 1]
  /\ coarseHeld' = FALSE
  /\ fineHeld' = NoFeeder
  /\ UNCHANGED ceiling

\* The operator can only move the ceiling between lock-chains, not mid-commit,
\* so an in-flight fine-lock decision is never invalidated out from under it.
RaiseCeiling ==
  /\ ~coarseHeld
  /\ ceiling < HardCap
  /\ ceiling' = ceiling + 1
  /\ UNCHANGED <<load, coarseHeld, fineHeld>>

LowerCeiling ==
  /\ ~coarseHeld
  /\ ceiling > 0
  /\ ceiling' = ceiling - 1
  /\ UNCHANGED <<load, coarseHeld, fineHeld>>

AnyAcquireFine == \E f \in Feeders : AcquireFine(f)
AnyShedRelease == \E f \in Feeders : ShedRelease(f)

Next ==
  \/ AcquireCoarse
  \/ AnyAcquireFine
  \/ AnyShedRelease
  \/ \E f \in Feeders : RestoreRelease(f)
  \/ RaiseCeiling
  \/ LowerCeiling

\* Fairness on the lock-and-shed chain drives the shedder to make progress
\* whenever it stays enabled, without forcing quantified per-feeder clauses.
Spec == Init /\ [][Next]_Vars
             /\ WF_Vars(AcquireCoarse)
             /\ WF_Vars(AnyAcquireFine)
             /\ WF_Vars(AnyShedRelease)

\* The grid's fixed physical capacity limit is never exceeded.
CapacityBound == TotalLoad <= HardCap

\* Whenever load exceeds the operator's current ceiling, it is eventually shed back.
CeilingRecovers == (TotalLoad > ceiling) ~> (TotalLoad <= ceiling)
====