---- MODULE W4Od3m0p0t0 ----
EXTENDS Naturals
CONSTANTS Banks, Ledger, Lock
VARIABLES snapshot, lastBank
vars == <<Banks, Ledger, Lock, snapshot, lastBank>>

Init ==
    /\ snapshot = [b \in Banks |-> "free"]
    /\ lastBank = "none"
    /\ \A b \in Banks : b \in Banks /\ "idle" \in b

Next ==
    /\ \E b \in Banks : b \in Banks /\ "idle" \in b /\ snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"reading"}}
    /\ \A b \in Banks : b \in Banks /\ snapshot[b] = "reading" /\ snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"trying"}}
    /\ \A b \in Banks : b \in Banks /\ snapshot[b] = "trying" /\ snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"holding"}}
    /\ \A b \in Banks : b \in Banks /\ snapshot[b] = "holding" /\ snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \A b \in Banks : b \in Banks /\ snapshot[b] = "posting" /\ snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"idle"}}
    /\ \A b \in Banks : b \in Banks /\ snapshot[b] = "idle" /\ snapshot' = snapshot
    /\ \A b \in Banks : b \in Banks /\ snapshot[b] = "free" /\ snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"reading"}}
    /\ \A b \in Banks : b \in Banks /\ snapshot[b] = "reading" /\ snapshot' = snapshot
    /\ \A b \in Banks : b \in Banks /\ snapshot[b] = "trying" /\ snapshot' = snapshot
    /\ \A b \in Banks : b \in Banks /\ snapshot[b] = "holding" /\ snapshot' = snapshot
    /\ \A b \in Banks : b \in Banks /\ snapshot[b] = "posting" /\ snapshot' = snapshot
    /\ \A b \in Banks : b \in Banks /\ snapshot[b] = "idle" /\ snapshot' = snapshot
    /\ Lock' = "none"
    /\ \A b \in Banks : b \in Banks /\ snapshot[b] = "holding" /\ snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"idle"}}
    /\ \A b \in Banks : b \in Banks /\ snapshot[b] = "posting" /\ snapshot' = snapshot
    /\ \A b \in Banks : b \in Banks /\ snapshot[b] = "idle" /\ snapshot' = snapshot
    /\ \A b \in Banks : b \in Banks /\ snapshot[b] = "free" /\ snapshot' = snapshot
    /\ \A b \in Banks : b \in Banks /\ snapshot[b] = "reading" /\