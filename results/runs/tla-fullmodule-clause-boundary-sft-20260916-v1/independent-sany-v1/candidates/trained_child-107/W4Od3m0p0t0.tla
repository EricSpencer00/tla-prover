---- MODULE W4Od3m0p0t0 ----
EXTENDS Naturals
CONSTANTS Banks, Ledger, Lock
VARIABLES snapshot, holder
vars == <<snapshot, holder>>

Init ==
    /\ snapshot = "none"
    /\ holder = "none"
    /\ \A b \in Banks : b \in Ledger

Next ==
    /\ snapshot' = snapshot
    /\ holder' = holder
    /\ \A b \in Ledger : b' = b
    /\ \A b \A b' \in Banks : b' \in Ledger'
    /\ \A b \in Lock : b' \in Lock'
    /\ \A b \A l \in Banks : l \in Ledger => l \in Ledger'
    /\ \E b \in Banks : b \notin Ledger => b \in Ledger'
    /\ \D b \in Banks : b \# "none" => b \in Banks'
    /\ \E b \A l \in Banks :
        /\ snapshot = l
        /\ Lock = "none"
        /\ snapshot' = l
        /\ holder' = l
        /\ UNCHANGED <<snapshot, holder>>
    /\ \E b \A o \in Banks :
        /\ snapshot # l
        /\ Lock = l
        /\ snapshot' = l
    /\ \E b \A h \in Banks :
        /\ snapshot' = h
        /\ holder' = h
        /\ snapshot = h
        /\ Lock = "none"

Spec == Init /\ [][Next]_vars

MutEx == Init /\ [][Next]_\vars => \A b \in Banks : holder = "none" \/ holder = b

====