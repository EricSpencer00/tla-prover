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
    \/ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \A b \in Banks : snapshot[b] \in {"free", "reading", "posting"}
    /\ \A b \in Banks : snapshot' \in {"idle"} \cup {"reading"} \cup {"posting"}
    /\ \A b \in Banks : snapshot' \in {"idle"} \cup {"reading"} \cup {"posting"} => snapshot[b] \in {"idle"} \cup {"reading"} \cup {"posting"}
    /\ \A b \in Banks : snapshot' \in {"idle"} \cup {"reading"} \cup {"posting"} => snapshot' \in {"idle"} \cup {"reading"} \cup {"posting"}
    /\ \A b \in Banks : snapshot' \in {"idle"} \cup {"reading"} \cup {"posting"} => snapshot[b] \in {"idle"} \cup {"reading"} \cup {"posting"}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"idle"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"crashed"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"rebooting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ Lock' = "none"
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => Lock' = b
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}}
    /\ \E b \in Banks : snapshot' = snapshot \cup {b |-> snapshot[b] \cup {"posting"}} => snapshot' =