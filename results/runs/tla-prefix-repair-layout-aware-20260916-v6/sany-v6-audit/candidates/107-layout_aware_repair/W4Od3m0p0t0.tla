---- MODULE W4Od3m0p0t0 ----
EXTENDS Naturals
CONSTANTS Banks, Ledger, Lock
VARIABLES snapshot, holder
vars == <<snapshot, holder>>

Init == snapshot = [b \in Banks |-> "free"] /\ holder = "none"

Next == \/ crash(b) \/ idle(b) \/ post(b)
crash(b) == snapshot' = snapshot /\ holder' = "none"
idle(b) == snapshot' = snapshot /\ holder' = "none" /\ snapshot[b] = "free"
post(b) == snapshot' = snapshot \/ snapshot' = [snapshot EXCEPT![b] = "held"] 
          /\ holder' = "none" \/ holder' = b
          /\ UNCHANGED <<snapshot EXCEPT [b, holder, holder \in Banks |-> "none"]\*>>

\* Critical section invariant
\* At most one bank holds the lock
\* A bank holds the lock only when the snapshot names it
\* A bank holds the lock only when the snapshot is up to date
\* A bank that crashed and rebooted does not hold the lock
\* A bank that crashed and rebooted has an up to date snapshot
\* A bank that crashed and rebooted is idle
\* A bank that crashed and rebooted is not the holder
\* A bank that crashed and rebooted is not the holder of the crashed bank
\* A bank that crashed and rebooted has an up to date snapshot of the crashed bank
\* A bank that crashed and rebooted has an up to date snapshot of the holder
\* A bank that crashed and rebooted has an up to date snapshot of the banks that crashed and rebooted
\* A bank that crashed and rebooted has an up to date snapshot of the banks that are idle
\* A bank that crashed and rebooted has an up to date snapshot of the banks that are posting
\* A bank that crashed and rebooted has an up to date snapshot of the banks that are holding the lock
\* A bank that crashed and rebooted has an up to date snapshot of the banks that are holding the lock and crashed and rebooted
\* A bank that crashed and rebooted has an up to date snapshot of the banks that are holding the lock and idle
\* A bank that crashed and rebooted has an up to date snapshot of the banks that are holding the lock and posting
\* A bank that crashed and rebooted has an up to date snapshot of the banks that are holding the lock and crashed and rebooted and idle
\* A bank that crashed and rebooted has an up to date snapshot of the banks that are holding the lock and crashed and rebooted and posting
\* A bank that crashed and rebooted has an up to date snapshot of the banks that are holding the lock and idle and posting
\* A bank that crashed and rebooted has an up to date snapshot of the banks that are holding the lock and idle and crashed and rebooted
\* A bank that crashed and rebooted has an up to date snapshot of the