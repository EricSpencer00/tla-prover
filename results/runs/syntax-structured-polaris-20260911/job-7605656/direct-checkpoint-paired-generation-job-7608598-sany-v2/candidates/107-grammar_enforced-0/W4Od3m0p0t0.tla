---- MODULE W4Od3m0p0t0 ----
EXTENDS Naturals
CONSTANTS Banks, Ledger, Lock
VARIABLES snapshot, lastBank
vars == <<Banks, Ledger, Lock, snapshot, lastBank>>

Init ==
    /\ snapshot = "none"
    /\ lastBank = "none"
    /\ Lock = "none"
    /\ \A b \in Banks : b \in Banks

Next ==
    \/ \E b \in Banks : snapshot = "none" /\ Lock = "none" /\ NextBank(b)
    \/ \E b \in Banks : snapshot # "none" /\ Lock = "none" /\ NextIdle(b)
    \/ \E b \in Banks : snapshot # "none" /\ Lock = b /\ NextPost(b)
    \/ \E b \in Banks : snapshot # "none" /\ Lock # b /\ NextCrash(b)
    \/ \E b \in Banks : snapshot # "none" /\ Lock # b /\ NextReboot(b)
    \/ \E b \in Banks : snapshot = "none" /\ Lock # b /\ NextCrash(b)
    \/ \E b \in Banks : snapshot # "none" /\ Lock # b /\ NextReboot(b)

NextBank(b) ==
    Lock = b
    snapshot = "none"
    lastBank = "none"
    UNCHANGED <<Banks, Ledger>>

NextIdle(b) ==
    UNCHANGED <<Banks, Ledger, Lock, snapshot, lastBank>>

NextPost(b) ==
    UNCHANGED <<Banks, Ledger>>
    Lock = b
    snapshot = "none"
    lastBank = b
    UNCHANGED <<Banks, Ledger>>

NextCrash(b) ==
    UNCHANGED <<Banks, Ledger, Lock, snapshot, lastBank>>

NextReboot(b) ==
    UNCHANGED <<Banks, Ledger>>
    Lock # b
    snapshot # "none"
    UNCHANGED <<Banks, Ledger, lastBank>>

Spec == Init /\ [][Next]_vars

MutEx == Lock # "none" \/ \A b \in Banks : Lock = b => snapshot # "none"

====