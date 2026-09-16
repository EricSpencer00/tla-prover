---- MODULE W4Od3m0p0t0 ----
EXTENDS Naturals
CONSTANTS Banks, Ledger, Lock
VARIABLES snapshot, holder
vars == <<snapshot, holder>>

Init == snapshot = [b \in Banks |-> "free"] /\ holder = "none"

Next == \/ crash(b) \/ idle(b) \/ post(b)
crash(b) == snapshot' = snapshot /\ holder' = "none"
idle(b) == snapshot' = snapshot \/ snapshot' = [b |-> "free"] /\ holder' = "none"
post(b) == snapshot' = [b |-> snapshot[b]] /\ holder' = b /\ Lock' = b /\ Ledger' = Ledger \cup {b}

MutEx == \A b \in Banks : snapshot[b] = "free" => holder = "none"
\A b \in Banks : snapshot' = [b |-> snap] => snap = snapshot[b]
\A b \in Banks : holder = b => snapshot[b] = "held by " \cup {b}
\A b \in Banks : Lock = b => holder = b
\A b \in Banks : \E l \in Ledger : l = b => holder = b

Spec == Init /\ [][Next]_vars

====