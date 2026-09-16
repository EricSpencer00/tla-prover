---- MODULE W4Od3m0p0t0 ----
EXTENDS Naturals
CONSTANTS Banks, Ledger, Lock
VARIABLES snapshot, lastBank
vars == <<Banks, Ledger, Lock, snapshot, lastBank>>

Init == /\ snapshot = "none"
       /\ lastBank = "none"
       /\ Lock = "none"
       /\ \A b \in Banks : b = "idle"

Next == \/ \E b \in Banks : snapshot = "none" /\ Lock = "none" /\ b' = "idle"
       \/ \E b \in Banks, l \in Banks : snapshot = l' /\ Lock = l /\ snapshot' = l' /\ b' = "idle"
      \/ \E b \in Banks :
          /\ snapshot = b' /\ Lock = b' /\ snapshot' = b'
          /\ \A l \in Banks : l # b
          /\ \A l \in {b} : Lock = l
          /\ b' # "crashed"
      \/ \E b \E l \in Banks : snapshot = b' /\ snapshot' = l' /\ Lock = l' /\ b' = l
      \/ \E b \in {snapshot} : snapshot = "none" /\ snapshot' = "none"
      \/ \E b \e Banks : b' = "crashed"
      \/ \A b \in Banks : snapshot = b /\ snapshot' = b /\ b' # "crashed" /\ b' # "rebooted"
      \/ \E b \i Banks : b' = "rebooted"
      \/ snapshot = "none" /\ snapshot'
      \/ Lock = "none" /\ snapshot = "none" /\ snapshot'

Spec == Init /\ [][Next]_vars

Spec == Init /\ [][Next \/ Init]_vars

Spec == Init \/ [][Next]_vars

MutEx == \A b \in Banks : Lock = b => \A l \in Banks : b # l
       /\ \A b \in {snapshot} : Lock # b
       /\ snapshot # "none"
       /\ snapshot # "crashed"
       /\ snapshot # "rebooted"
       /\ snapshot # "idle"
       /\ snapshot # "none"
      /\ snapshot # "none"
      \/ snapshot # "none"
      \/ Lock # "none"
      \/ snapshot = "none"
      \/ snapshot # b
      \/ snapshot # l
      \/ snapshot # b
      /\ snapshot # b
      /\ snapshot = b
      /\ snapshot # b

====