---- MODULE W4Od3m0p0t0 ----
EXTENDS Naturals
CONSTANTS Banks, Ledger, Lock
VARIABLES snapshot, holder
vars == <<snapshot, holder>>

Init == snapshot = [b \in Banks |-> "free"] /\ holder = "none"

Next == \/ crash(b) \/ idle(b) \/ post(b)
crash(b) == snapshot' = snapshot /\ holder' = "none"
idle(b) == snapshot' = snapshot /\ holder' = "none" /\ snapshot[b] = "free"
post(b) == (snapshot' = snapshot \/ snapshot' = [snapshot EXCEPT![b] = "held"]) /\ holder' = b
lock(b) == snapshot' = [snapshot EXCEPT![b] = "held"] /\ holder' = b
release(b) == snapshot' = [snapshot EXCEPT![b] = "free"] /\ holder' = "none"
reboot(b) == snapshot' = snapshot /\ holder' = "none"

Spec == Init /\ [][Next]_vars

MutEx == \A b \in Banks : snapshot[b] = "held" => holder = b
\A b \in Banks : snapshot[b] = "free" => holder = "none"
\A b \in Banks : snapshot' = snapshot => holder' = holder
\A b \in Banks : holder = b => \E c \in Banks : snapshot[c] = "held"

====