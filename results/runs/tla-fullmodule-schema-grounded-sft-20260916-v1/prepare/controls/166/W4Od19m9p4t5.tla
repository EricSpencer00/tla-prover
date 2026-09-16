---- MODULE W4Od19m9p4t5 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Books, HardCap, MaxEpoch, OverrideBudget

VARIABLES epoch, capacity, reservations, overrideCount, adminEnabled

vars == <<epoch, capacity, reservations, overrideCount, adminEnabled>>

\* Epoch-numbered reconfiguration: capacity never resets below books already held.
Init ==
  /\ epoch = 0
  /\ capacity = HardCap
  /\ reservations = {}
  /\ overrideCount = 0
  /\ adminEnabled = FALSE

Reserve(b) ==
  /\ b \in Books
  /\ b \notin reservations
  /\ Cardinality(reservations) < capacity
  /\ reservations' = reservations \cup {b}
  /\ UNCHANGED <<epoch, capacity, overrideCount, adminEnabled>>

Release(b) ==
  /\ b \in reservations
  /\ reservations' = reservations \ {b}
  /\ UNCHANGED <<epoch, capacity, overrideCount, adminEnabled>>

\* Admin override bypasses the soft cap, bounded by the hard cap and a per-epoch budget.
AdminOverrideReserve(b) ==
  /\ adminEnabled
  /\ overrideCount < OverrideBudget
  /\ b \in Books
  /\ b \notin reservations
  /\ Cardinality(reservations) < HardCap
  /\ reservations' = reservations \cup {b}
  /\ overrideCount' = overrideCount + 1
  /\ UNCHANGED <<epoch, capacity, adminEnabled>>

AdminRevoke(b) ==
  /\ adminEnabled
  /\ b \in reservations
  /\ reservations' = reservations \ {b}
  /\ UNCHANGED <<epoch, capacity, overrideCount, adminEnabled>>

Reconfigure ==
  /\ epoch < MaxEpoch
  /\ epoch' = epoch + 1
  /\ capacity' \in (IF Cardinality(reservations) = 0 THEN 1 ELSE Cardinality(reservations))..HardCap
  /\ overrideCount' = 0
  /\ adminEnabled' \in BOOLEAN
  /\ UNCHANGED reservations

Next ==
  \/ \E b \in Books : Reserve(b)
  \/ \E b \in Books : Release(b)
  \/ \E b \in Books : AdminOverrideReserve(b)
  \/ \E b \in Books : AdminRevoke(b)
  \/ Reconfigure

Spec == Init /\ [][Next]_vars

\* Held reservations stay under the hard cap; absent an override this
\* epoch, they also respect the epoch's own soft capacity.
CapacityInvariant ==
  /\ Cardinality(reservations) <= HardCap
  /\ (overrideCount = 0 => Cardinality(reservations) <= capacity)

====