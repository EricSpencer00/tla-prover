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
    /\ \E b \in Banks : b \in Banks /\ "idle" \in b /\ snapshot' = snapshot \cup {b | snapshot[b] = "free"}
    /\ \A b \in Banks : snapshot' \in {"idle", "posting"}
    /\ \A b \in Banks : snapshot' \in {"idle", "posting"} => snapshot[b] \in {"idle", "posting"}
    /\ \A b \in Banks : snapshot' \in {"idle", "posting"} => snapshot' \in {"idle", "posting"}
    /\ \A b \in Banks : snapshot' \in {"idle", "posting"} => snapshot' \in {"idle", "posting"}
    /\ \A b \in Banks : snapshot' \in {"idle", "posting"} => snapshot' \in {"idle", "posting"}
    /\ \A b \in Banks : snapshot' \in {"idle", "posting"} => snapshot' \in {"idle", "posting"}
    /\ \A b \in Banks : snapshot' \in {"idle", "posting"} => snapshot' \in {"idle", "posting"}
    /\ \A b \in Banks : snapshot' \in {"idle", "posting"} => snapshot' \in {"idle", "posting"}
    /\ \A b \in Banks : snapshot' \in {"idle", "posting"} => snapshot' \in {"idle", "posting"}
    /\ \A b \in Banks : snapshot' \in {"idle", "posting"} => snapshot' \in {"idle", "posting"}
    /\ \A b \in Banks : snapshot' \in {"idle", "posting"} => snapshot' \in {"idle", "posting"}
    /\ \A b \in Banks : snapshot' \in {"idle", "posting"} => snapshot' \in {"idle", "posting"}
    /\ \A b \in Banks : snapshot' \in {"idle", "posting"} => snapshot' \in {"idle", "posting"}
    /\ \A b \in Banks : snapshot' \in {"idle", "posting"} => snapshot' \in {"idle", "posting"}
    /\ \A b \in Banks : snapshot' \in {"idle", "posting"} => snapshot' \in {"idle", "posting"}
    /\ \A b \in Banks : snapshot' \in {"idle", "posting"} => snapshot' \in {"idle", "posting"}
    /\ \A b \in Banks : snapshot' \in {"idle", "posting"} => snapshot' \in {"idle", "posting"}
    /\ \A b