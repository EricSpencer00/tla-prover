---- MODULE W4Od3m0p0t0 ----
EXTENDS Integers

Banks == {"b1", "b2", "b3"}
NONE == "none"

VARIABLES lock, status, snap, ledger
vars == <<lock, status, snap, ledger>>

Init ==
    /\ lock = NONE
    /\ status = [b \in Banks |-> "idle"]
    /\ snap = [b \in Banks |-> NONE]
    /\ ledger = NONE

Read(b) ==
    /\ status[b] = "idle"
    /\ status' = [status EXCEPT ![b] = "trying"]
    /\ snap' = [snap EXCEPT ![b] = lock]
    /\ UNCHANGED <<lock, ledger>>

Acquire(b) ==
    /\ status[b] = "trying"
    /\ snap[b] = NONE
    /\ lock = NONE
    /\ lock' = b
    /\ status' = [status EXCEPT ![b] = "cs"]
    /\ UNCHANGED <<snap, ledger>>

Retry(b) ==
    /\ status[b] = "trying"
    /\ snap[b] # lock
    /\ snap' = [snap EXCEPT ![b] = lock]
    /\ UNCHANGED <<lock, status, ledger>>

Exit(b) ==
    /\ status[b] = "cs"
    /\ lock = b
    /\ lock' = NONE
    /\ status' = [status EXCEPT ![b] = "idle"]
    /\ ledger' = b
    /\ UNCHANGED snap

Crash(b) ==
    /\ status[b] # "crashed"
    /\ status' = [status EXCEPT ![b] = "crashed"]
    /\ UNCHANGED <<lock, snap, ledger>>

Recover(b) ==
    /\ status[b] = "crashed"
    /\ status' = [status EXCEPT ![b] = "idle"]
    /\ lock' = IF lock = b THEN NONE ELSE lock
    /\ snap' = [snap EXCEPT ![b] = NONE]
    /\ UNCHANGED ledger

Next ==
    \/ \E b \in Banks : Read(b)
    \/ \E b \in Banks : Acquire(b)
    \/ \E b \in Banks : Retry(b)
    \/ \E b \in Banks : Exit(b)
    \/ \E b \in Banks : Crash(b)
    \/ \E b \in Banks : Recover(b)

Spec == Init /\ [][Next]_vars

TypeOK ==\n    /\ lock \in Banks \cup {NONE}
    /\ lock \in Banks \cup {NONE}
    /\ status \in [Banks -> {"idle","trying","cs","crashed"}]
    /\ snap \in [Banks -> Banks \cup {NONE}]
    /\ ledger \in Banks \cup {NONE}

MutEx ==
    \A b \in Banks : (status[b] = "cs") => (lock = b)

====