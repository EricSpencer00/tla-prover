---- MODULE W4Od3m0p0t0 ----
EXTENDS Naturals
CONSTANTS Banks, Ledger, Lock
VARIABLES snapshot, lastBank
vars == <<Banks, Ledger, Lock, snapshot, lastBank>>

Init ==
    /\ snapshot = "none"
    /\ \A b \in Banks : lastBank = "none"
    /\ Lock = "none"
    /\ Ledger = "none"

Next ==
    /\ \E b \in Banks : snapshot = "none" /\ Lock = "none"
    \/ \E b \in Banks : /\ snapshot = "none" /\ Lock \in Banks /\ snapshot' = snapshot /\ Lock' = Lock /\ snapshot' \in {"none", Lock}
    \/ \E b \in snapshot : /\ snapshot \in Banks /\ snapshot \in {"none", Lock} /\ snapshot' = snapshot /\ snapshot' \in {"none"}
    \/ \E b \in lastBank : /\ snapshot \in Banks /\ Lock = snapshot /\ snapshot' = snapshot /\ snapshot \in {"none"}
    \/ /\ snapshot \in Banks /\ snapshot' = "none"
    \/ /\ snapshot \in Banks : /\ snapshot \in {"none", \A b \in Banks : b \neq snapshot : b} /\ snapshot' = snapshot /\ Lock = snapshot
    \/ /\ snapshot \in Banks :snapshot \in {"none", Lock} : /\ snapshot \in {"none"}
      /\ snapshot' = snapshot /\ snapshot = "none"
    \/ /\ Lock \in Banks /\ snapshot = "none" /\ snapshot' = snapshot /\ snapshot'' \in {"none", Lock}
      /\ snapshot' \in {"none"} /\ snapshot'' \in {"none"}
    \/ snapshot \in Banks /\ snapshot' \in {"none"}

Spec == Init /\ [][Next]_vars

====