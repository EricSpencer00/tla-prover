---- MODULE W4Od3m0p0t0 ----
EXTENDS Naturals
CONSTANTS Banks, Ledger, Lock
VARIABLES snapshot, lastBank
vars == <<Banks, Ledger, Lock, snapshot, lastBank>>

Init ==
    /\ snapshot = "none"
    /\ lastBank = "none"
    /\ Lock = "none"
    /\ \A b \in Banks : b = "idle"

Next ==
    /\ snapshot' = snapshot
    \/ snapshot' = "none"
    /\ UNCHANGED <<Banks, Ledger, lastBank>>

Spec == Init /\ [][Next]_vars

MutEx == Init /\ [][Next]_vars
    /\ \A b \in Banks : snapshot = "none" => Lock = "none"
    /\ \A b \in Banks : snapshot = b => Lock = b
    /\ \A b \in Banks : snapshot = b => lastBank = b
    /\ \A b \in Banks : snapshot = b => \A b' \in Banks : b' # b => snapshot' = b'

====